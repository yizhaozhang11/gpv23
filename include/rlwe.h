#ifndef RLWE_H
#define RLWE_H

#include "dcrtpoly.h"
#include <concepts>

template <typename DCRT>
using RLWECiphertext = std::array<DCRT, 2>;

template <typename DCRT>
RLWECiphertext<DCRT> RLWEEncrypt(const DCRT &m, const DCRT &s) {
    auto a = DCRT::SampleUniform();
    auto e = DCRT::SampleE();
    return {a, a * s + m + e};
}

template <typename DCRT>
using RLWEGadgetCiphertext = std::array<RLWECiphertext<DCRT>, DCRT::ell>;

template <typename DCRT>
using RGSWCiphertext = std::array<RLWEGadgetCiphertext<DCRT>, 2>;

template <typename DCRT>
RLWEGadgetCiphertext<DCRT> RLWEGadgetEncrypt(const DCRT &m, const DCRT &s) {
    RLWEGadgetCiphertext<DCRT> c;
    DCRT::U::ForEach([&c, &m, &s]<size_t i> {
        c[i] = RLWEEncrypt(m.template Component<typename DCRT::template NTTi<i>>(), s);
    });
    return c;
}

template <typename DCRT>
RGSWCiphertext<DCRT> RGSWEncrypt(const DCRT &m, const DCRT &s) {
    return {RLWEGadgetEncrypt(m * s, s), RLWEGadgetEncrypt(m, s)};
}

template <typename DCRT>
RLWECiphertext<DCRT> Mult(const DCRT &a, const RLWEGadgetCiphertext<DCRT> &c) {
    RLWECiphertext<DCRT> res;
    DCRT::U::ForEach([&res, &a, &c]<size_t i> {
        auto ai = a.template BaseExtend<typename DCRT::template NTTi<i>>();
        res[0] = res[0] + c[i][0] * ai;
        res[1] = res[1] + c[i][1] * ai;
    });
    return res;
}

// TODO: Improve this function
template <typename DCRT>
RLWEGadgetCiphertext<DCRT> GadgetMult(const DCRT &a, const RLWEGadgetCiphertext<DCRT> &c) {
    RLWEGadgetCiphertext<DCRT> res;
    DCRT::U::ForEach([&res, &a, &c]<size_t i> {
        res[i] = Mult(a.template Component<typename DCRT::template NTTi<i>>(), c);
    });
    return res;
}

template <typename DCRT>
inline RLWECiphertext<DCRT> ExtMult(const RLWECiphertext<DCRT> &c, const RGSWCiphertext<DCRT> &C) {
    RLWECiphertext<DCRT> res;
    DCRT::U::ForEach([&res, &c, &C]<size_t i> {
        auto ai = c[0].template BaseExtend<typename DCRT::template NTTi<i>>();
        auto bi = c[1].template BaseExtend<typename DCRT::template NTTi<i>>();
        res[0] = res[0] - C[0][i][0] * ai + C[1][i][0] * bi;
        res[1] = res[1] - C[0][i][1] * ai + C[1][i][1] * bi;
    });
    return res;
}

template <typename DCRT>
RLWEGadgetCiphertext<DCRT> ExtMult(const RLWEGadgetCiphertext<DCRT> &c, const RGSWCiphertext<DCRT> &C) {
    RLWEGadgetCiphertext<DCRT> res;
    DCRT::U::ForEach([&res, &c, &C]<size_t i> {
        res[i] = ExtMult(c[i], C);
    });
    return res;
}

template <typename DCRT>
RLWEGadgetCiphertext<DCRT> KeySwitchGen(const DCRT &s, const DCRT &snew) {
    return RLWEGadgetEncrypt(s, snew);
}

template <typename DCRT>
RLWECiphertext<DCRT> KeySwitch(const RLWECiphertext<DCRT> &c, const RLWEGadgetCiphertext<DCRT> &K) {
    RLWECiphertext<DCRT> res;
    res[1] = c[1];
    DCRT::U::ForEach([&res, &c, &K]<size_t i> {
        auto ci = c[0].template BaseExtend<typename DCRT::template NTTi<i>>();
        res[0] = res[0] - K[i][0] * ci;
        res[1] = res[1] - K[i][1] * ci;
    });
    return res;
}

template <typename DCRT>
RLWEGadgetCiphertext<DCRT> KeySwitch(const RLWEGadgetCiphertext<DCRT> &c, const RLWEGadgetCiphertext<DCRT> &K) {
    RLWEGadgetCiphertext<DCRT> res;
    DCRT::U::ForEach([&res, &c, &K]<size_t i> {
        res[i] = KeySwitch(c[i], K);
    });
    return res;
}

template <typename DCRT>
RGSWCiphertext<DCRT> SchemeSwitch(const RLWEGadgetCiphertext<DCRT> &c, const RLWEGadgetCiphertext<DCRT> &Ksk) {
    RLWEGadgetCiphertext<DCRT> res;
    DCRT::U::ForEach([&res, &c, &Ksk]<size_t i> {
        res[i] = Mult(c[i][0], Ksk);
        res[i][0] = res[i][0] * (-1);
        res[i][1] = res[i][1] * (-1);
        res[i][0] = res[i][0] - c[i][1];
    });
    return {res, c};
}

template <typename T, template <typename...> typename U>
struct is_instantiation_of : std::false_type {};

template <template <typename...> typename U, typename... T>
struct is_instantiation_of<U<T...>, U> : std::true_type {};

template <typename DCRT>
RLWECiphertext<DCRT> Galois(const RLWECiphertext<DCRT> &c, size_t alpha) requires is_instantiation_of<DCRT, DCRTPoly>::value {
    RLWECiphertext<DCRT> res;
    res[0] = c[0].Galois(alpha);
    res[1] = c[1].Galois(alpha);
    return res;
}

template <typename DCRT>
RLWEGadgetCiphertext<DCRT> Galois(const RLWEGadgetCiphertext<DCRT> &c, size_t alpha) {
    RLWEGadgetCiphertext<DCRT> res;
    DCRT::U::ForEach([&res, &c, alpha]<size_t i> {
        res[i] = Galois(c[i], alpha);
    });
    return res;
}

template <typename DCRT>
RGSWCiphertext<DCRT> Galois(const RGSWCiphertext<DCRT> &c, size_t alpha) {
    RGSWCiphertext<DCRT> res;
    res[0] = Galois(c[0], alpha);
    res[1] = Galois(c[1], alpha);
    return res;
}

template <typename DCRT>
void DecryptAndPrint(const RLWEGadgetCiphertext<DCRT> &c, const DCRT &s) {
    DCRT::U::ForEach([&c, &s]<size_t i> {
        auto mi = c[i][1] - c[i][0] * s;
        mi = mi * DCRT::D_factors[i][i];
        auto m = mi.template ModulusSwitch<typename DCRT::template NTTi<i>>();
        m.Print();
    });
}

template <typename DCRT>
void DecryptAndTest(const RLWECiphertext<DCRT> &c, const DCRT &s, const uint64_t t_plain, const Poly<DCRT::N> &bt_poly, size_t b) {
    auto m = (c[1] - c[0] * s).template ModulusSwitch<typename DCRT::template NTTi<0>>();
    for (size_t i = 0; i < DCRT::N; i++) {
        auto z = (m.a[i] * t_plain + DCRT::p[0] / 2) / DCRT::p[0] % t_plain;
        if (z != (uint64_t)bt_poly.a[(i + b) % DCRT::N]) {
            std::cout << "Error: " << i << " " << z << " " << bt_poly.a[i] << std::endl;
        }
    }
}

#endif // RLWE_H