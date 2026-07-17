#!/usr/bin/env sage

"""Discover compact principal-ideal certificates in Q(zeta_23)^+.

The output is JSON on stdout.  Sage is used only for discovery: the Node
validator and Lean's kernel independently recheck the serialized witnesses.
"""

import json


BOUND = 900
PRIMES = [q for q in prime_range(2, BOUND + 1)
          if q != 23 and q % 23 in (1, 22)]
assert PRIMES == [47, 137, 139, 229, 277, 367, 461, 599, 643, 691, 827, 829]

R.<X> = PolynomialRing(ZZ)
f = X^11 - X^10 - 10*X^9 + 9*X^8 + 36*X^7 - 28*X^6 \
    - 56*X^5 + 35*X^4 + 35*X^3 - 15*X^2 - 6*X + 1
K.<a> = NumberField(f)


def coefficients(poly):
    """Serialize a polynomial's ascending coefficients without trailing zeroes."""
    if poly == 0:
        return []
    return [str(poly[index]) for index in range(poly.degree() + 1)]


def integral_polynomial(element):
    """Write an integral power-basis element as a polynomial in a."""
    values = list(K(element))
    assert all(value.denominator() == 1 for value in values), values
    return R([ZZ(value) for value in values])


def certificate_for_ideal(q, ideal):
    """Build and internally check one certificate for a degree-one prime ideal."""
    assert ideal.norm() == q

    _, ideal_polynomial_element = ideal.gens_two()
    P = integral_polynomial(ideal_polynomial_element)
    if P.leading_coefficient() == -1:
        P = -P
    assert P.is_monic() and P.degree() == 1
    balanced_constant = ZZ(P[0] % q)
    if balanced_constant > q // 2:
        balanced_constant -= q
    P = X + balanced_constant

    generator = ideal.gens_reduced()[0]
    G = integral_polynomial(generator)
    norm = ZZ(generator.norm())
    assert abs(norm) == q

    Qq = integral_polynomial(K(q) / generator)
    Rq, remainder_q = (R(q) - G * Qq).quo_rem(f)
    assert remainder_q == 0

    QP = integral_polynomial(K(P(a)) / generator)
    RP, remainder_P = (P - G * QP).quo_rem(f)
    assert remainder_P == 0

    C1, remainder_G = G.quo_rem(P)
    assert all(coefficient % q == 0 for coefficient in remainder_G)
    C2 = R([coefficient // q for coefficient in remainder_G])
    assert G == C1 * P + C2 * q

    Q, remainder_f = f.quo_rem(P)
    assert all(coefficient % q == 0 for coefficient in remainder_f)
    A = R([coefficient // q for coefficient in remainder_f])
    assert P * Q + q * A == f

    resultant = f.resultant(G)
    assert resultant == norm and abs(resultant) == q

    result = {
        "q": int(q),
        "norm": str(norm),
        "P": coefficients(P),
        "Q": coefficients(Q),
        "A": coefficients(A),
        "G": coefficients(G),
        "Qq": coefficients(Qq),
        "Rq": coefficients(Rq),
        "QP": coefficients(QP),
        "RP": coefficients(RP),
        "C1": coefficients(C1),
        "C2": coefficients(C2),
        "resultant_f_G": str(resultant),
    }
    witnesses = [P, Q, A, G, Qq, Rq, QP, RP, C1, C2]
    result["score"] = str(max(abs(coefficient)
                              for witness in witnesses
                              for coefficient in witness))
    return result


certificates = []
for q in PRIMES:
    ideals = K.primes_above(q)
    assert len(ideals) == 11
    candidates = [certificate_for_ideal(q, ideal) for ideal in ideals]
    # The serialized tie-breaker makes discovery deterministic even if Sage's
    # ideal ordering changes while the optimal score stays tied.
    certificates.append(min(
        candidates,
        key=lambda candidate: (ZZ(candidate["score"]),
                               json.dumps(candidate, sort_keys=True)),
    ))

payload = {
    "polynomial": coefficients(f),
    "field_discriminant": str(K.discriminant()),
    "class_number": str(K.class_number()),
    "certificates": certificates,
}
print(json.dumps(payload, separators=(",", ":")))
