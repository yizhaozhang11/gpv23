#include <iostream>
#include <vector>

#include "dcrtpoly.h"
#include "rlwe.h"

#include <chrono>

#define START_TIMER start = std::chrono::system_clock::now()
#define END_TIMER std::cout << "Time: " << (std::chrono::duration<double>(std::chrono::system_clock::now() - start).count()) << std::endl

std::chrono::time_point<std::chrono::system_clock> start;

constexpr size_t p = 12289;
constexpr size_t gp = 11;
// constexpr size_t p = 97;
// constexpr size_t gp = 5;

constexpr size_t N = 1024;
constexpr size_t Ncyc = N * 2;

using NTT1 = CircNTT<NTT23<562896521097217LL, 5LL, p, gp>>;
using NTT2 = CircNTT<NTT23<562881873395713LL, 10LL, p, gp>>;
using NTT3 = CircNTT<NTT23<562515680858113LL, 5LL, p, gp>>;
using NTT4 = CircNTT<NTT23<561944420499457LL, 5LL, p, gp>>;
// using NTT5 = CircNTT<NTT23<561504989454337LL, 5LL, p, gp>>;

using DCRT = DCRTPoly<NTT1, NTT2, NTT3, NTT4>;
// using DCRT = DCRTPoly<NTT1, NTT2, NTT3, NTT4, NTT5>;

using VecN = std::array<uint64_t, N>;
using Z = Zp<p>;

constexpr size_t rN = Z::Pow(gp, (p - 1) / Ncyc);
constexpr size_t rho = 32;
constexpr size_t Rx = 32;
constexpr uint64_t zeta = Z::Pow(rN, rho);

VecN PartialFourierTransform(VecN a, size_t rho) {
    size_t n = a.size();
    for (size_t i = n; i > rho; i >>= 1) {
        size_t j = i >> 1;
        size_t nn = n / i;
        uint64_t z = Z::Pow(rN, j);
        uint64_t w = Z::Pow(rN, i);
        for (size_t k = 0, kk = 0; k < nn; k++) {
            for (size_t l = 0; l < j; l++) {
                uint64_t u = Z::Mul(a[kk * i + l + j], z);
                a[kk * i + l + j] = Z::Sub(a[kk * i + l], u);
                a[kk * i + l] = Z::Add(a[kk * i + l], u);
            }
            for (size_t l = nn >> 1; l > (kk ^= l); l >>= 1);
            z = Z::Mul(z, w);
        }
    }
    return a;
}

VecN PartialInverseFourierTransform(VecN a, size_t rho, size_t r) {
    size_t n = a.size();
    std::vector<uint64_t> temp(r);
    std::vector<size_t> index;

    for (size_t i = rho; i < n; i *= r) {
        size_t j = std::min(i * r, n);
        r = j / i;
        uint64_t W = Z::Pow(rN, Ncyc - Ncyc / (j / rho));
        uint64_t w = Z::Pow(rN, Ncyc - Ncyc / r);
        if (r != index.size()) {
            index.resize(r);
            for (size_t k = 0, kk = 0; k < r; k++) {
                index[k] = kk;
                for (size_t l = r >> 1; l > (kk ^= l); l >>= 1);
            }
        }
        for (size_t k = 0; k < n; k += j) {
            uint64_t z = 1;
            for (size_t l = 0; l < i; l += rho) {
                for (size_t m = 0; m < rho; m++) {
                    uint64_t zz = z;
                    for (size_t f = 0; f < r; f++) {
                        auto &t = temp[f];
                        uint64_t zzz = zz;
                        t = a[k + l + m];
                        for (size_t g = 1; g < r; g++) {
                            t = Z::Add(t, Z::Mul(a[k + l + m + index[g] * i], zzz));
                            zzz = Z::Mul(zzz, zz);
                        }
                        zz = Z::Mul(zz, w);
                    }
                    for (size_t f = 0; f < r; f++) {
                        a[k + l + m + f * i] = temp[f];
                    }
                }

                z = Z::Mul(z, W);
            }
        }
    }

    uint64_t w = Z::Pow(rN, Ncyc - rho);
    uint64_t z = 1;
    for (size_t i = 0; i < n; i += rho) {
        for (size_t j = 0; j < rho; j++) {
            a[i + j] = Z::Mul(a[i + j], z);
        }
        z = Z::Mul(z, w);
    }

    return a;
}

using GaloisKey = std::vector<RLWEGadgetCiphertext<DCRT>>;

GaloisKey GaloisKeyGen(const DCRT &s) {
    GaloisKey Kg(p);
    for (size_t i = 2; i < p; i++) {
        Kg[i] = KeySwitchGen(s.Galois(i), s);
    }
    return Kg;
}

template <typename Ct>
Ct EvalInnerProduct(const GaloisKey &Kg, Ct ct, std::vector<RGSWCiphertext<DCRT>>::iterator z, uint64_t a0, std::vector<uint64_t>::iterator a, size_t l, size_t stride) {
    uint64_t t = a0;
    for (size_t i = 0; i < l; i++) {
        if (a[i] != 0) {
            t = Z::Mul(t, Z::Inv(a[i]));
            if (t != 1) {
                ct = Galois(ct, t);
                ct = KeySwitch(ct, Kg[t]);
            }
            ct = ExtMult(ct, z[i * stride]);
            t = a[i];
        }
    }
    if (t != 1) {
        ct = Galois(ct, t);
        ct = KeySwitch(ct, Kg[t]);
    }
    return ct;
}

RLWEGadgetCiphertext<DCRT> EvalInnerProduct(const GaloisKey &Kg, std::vector<RGSWCiphertext<DCRT>>::iterator z, std::vector<uint64_t>::iterator a, size_t l, size_t stride) {
    RLWEGadgetCiphertext<DCRT> ct = z[0][1];
    return EvalInnerProduct(Kg, ct, z + stride, a[0], a + 1, l - 1, stride);
}

std::vector<RLWECiphertext<DCRT>> HomomorphicPFT(const GaloisKey &Kg, const RLWEGadgetCiphertext<DCRT> Kss, std::vector<RLWEGadgetCiphertext<DCRT>> z, std::vector<RLWECiphertext<DCRT>> test, DCRT s) {
    std::vector<RGSWCiphertext<DCRT>> regs(N);
    std::vector<size_t> index;

    for (size_t i = rho; i < N; i *= Rx) {
        size_t j = std::min(i * Rx, N);
        size_t r = j / i;
        uint64_t W = Z::Pow(rN, Ncyc - Ncyc / (j / rho));
        uint64_t w = Z::Pow(rN, Ncyc - Ncyc / r);
        if (r != index.size()) {
            index.resize(r);
            for (size_t k = 0, kk = 0; k < r; k++) {
                index[k] = kk;
                for (size_t l = r >> 1; l > (kk ^= l); l >>= 1);
            }
        }
        for (size_t k = 0; k < N; k++) {
            regs[k] = SchemeSwitch(z[k], Kss);
        }
        if (j == N) {
            std::vector<uint64_t> adjust(N);
            {
                uint64_t w = Z::Pow(rN, Ncyc - rho);
                uint64_t Z = 1;
                for (size_t i = 0; i < N; i += rho) {
                    for (size_t j = 0; j < rho; j++) {
                        adjust[i + j] = Z;
                    }
                    Z = Z::Mul(Z, w);
                }
            }
            for (size_t k = 0; k < N; k += j) {
                uint64_t Z = 1;
                for (size_t l = 0; l < i; l += rho) {
                    for (size_t m = 0; m < rho; m++) {
                        uint64_t zz = Z;
                        for (size_t f = 0; f < r; f++) {
                            uint64_t zzz = 1;
                            std::vector<uint64_t> a(r);
                            for (size_t g = 0; g < r; g++) {
                                a[index[g]] = zzz * adjust[k + l + m + f * i] % p;
                                zzz = Z::Mul(zzz, zz);
                            }
                            test[k + l + m + f * i] = EvalInnerProduct(Kg, test[k + l + m + f * i], regs.begin() + k + l + m, 1, a.begin(), r, i);
                            zz = Z::Mul(zz, w);
                        }
                    }
                    Z = Z::Mul(Z, W);
                }
            }
        } else {
            for (size_t k = 0; k < N; k += j) {
                uint64_t Z = 1;
                for (size_t l = 0; l < i; l += rho) {
                    for (size_t m = 0; m < rho; m++) {
                        uint64_t zz = Z;
                        for (size_t f = 0; f < r; f++) {
                            uint64_t zzz = 1;
                            std::vector<uint64_t> a(r);
                            for (size_t g = 0; g < r; g++) {
                                a[index[g]] = zzz;
                                zzz = Z::Mul(zzz, zz);
                            }
                            z[k + l + m + f * i] = EvalInnerProduct(Kg, regs.begin() + k + l + m, a.begin(), r, i);
                            zz = Z::Mul(zz, w);
                        }
                    }
                    Z = Z::Mul(Z, W);
                }
            }
        }
    }

    return test;
}

int main() {
    VecN a, b0, z;
    for (size_t i = 0; i < N; i++) {
        z[i] = rand() % p;
        a[i] = rand() % p;
        b0[i] = 0;
    }
    for (size_t i = 0; i < N; i++) {
        std::cout << a[i] << " ";
    }
    std::cout << std::endl;
    for (size_t i = 0; i < N; i++) {
        std::cout << z[i] << " ";
    }
    std::cout << std::endl;
    VecN b = b0;
    for (size_t i = 0; i < N; i++) {
        for (size_t j = 0; j < N; j++) {
            if (i >= j) {
                b[i] = Z::Add(b[i], Z::Mul(a[j], z[i - j]));
            } else {
                b[i] = Z::Sub(b[i], Z::Mul(a[j], z[i + N - j]));
            }
        }
    }

    for (size_t i = 0; i < N; i++) {
        std::cout << b[i] << " ";
    }
    std::cout << std::endl;

    Poly<p> s_poly;
    for (size_t i = 0; i < N; i++) {
        s_poly.a[i] = rand() % 3 - 1;
    }
    DCRT s(s_poly);

    START_TIMER;

    GaloisKey Kg = GaloisKeyGen(s);
    RLWEGadgetCiphertext<DCRT> Kss = RLWEGadgetEncrypt(s * s, s);

    VecN aP = PartialFourierTransform(a, rho);
    VecN zP = PartialFourierTransform(z, rho);

    for (size_t i = 0; i < N; i++) {
        aP[i] = Z::Mul(aP[i], Z::Inv(N / rho));
    }

    std::vector<RGSWCiphertext<DCRT>> zz(N);
    for (size_t i = 0; i < N; i++) {
        zz[i] = RGSWEncrypt(DCRT::Monomial(zP[i], 1), s);
    }

    END_TIMER;

    START_TIMER;

    std::vector<RLWEGadgetCiphertext<DCRT>> regs(N);
    uint64_t zzeta = zeta;
    for (size_t k = 0, kk = 0; k < N / rho; k++) {
        for (size_t i = 0; i < rho; i++) {
            std::vector<uint64_t> a(rho);
            for (size_t j = 0; j <= i; j++) {
                a[i - j] = aP[kk * rho + j];
            }
            for (size_t j = i + 1; j < rho; j++) {
                a[rho - j + i] = Z::Mul(aP[kk * rho + j], zzeta);
            }
            regs[kk * rho + i] = EvalInnerProduct(Kg, zz.begin() + kk * rho, a.begin(), rho, 1);
        }
        zzeta = Z::Mul(zzeta, zeta);
        zzeta = Z::Mul(zzeta, zeta);
        for (size_t l = N / (2 * rho); l > (kk ^= l); l >>= 1);
    }

    END_TIMER;

    START_TIMER;

    Poly<p> bt_poly;
    bt_poly.a[1] = 1;
    DCRT at, bt{bt_poly};
    for (size_t j = 0; j < DCRT::N; j++) {
        bt.a[0][j] = NTT1::Z::Mul(bt.a[0][j], NTT1::Z::Mul(NTT1::p / 4, DCRT::D_factors[0][0]));
        for (size_t i = 1; i < DCRT::ell; i++) {
            bt.a[i][j] = 0;
        }
    }

    std::vector<RLWECiphertext<DCRT>> test(N, {at, bt});

    std::vector<RLWECiphertext<DCRT>> zPFT = HomomorphicPFT(Kg, Kss, regs, test, s);

    END_TIMER;

    for (size_t i = 0; i < N; i++) {
        std::cout << DecryptAndPrintE(zPFT[i], s) << " ";
    }
    std::cout << std::endl;

    return 0;
}