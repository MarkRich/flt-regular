# Fermat's Last Theorem for regular primes
The goal of this project is to prove Fermat's Last Theorem for [regular primes](https://en.wikipedia.org/wiki/Regular_prime)
in [Lean](https://leanprover-community.github.io/).

## Beal companion extension

The `BealRegular` library adds assumption-free, kernel-checked FLT coverage for
every equal exponent `3 <= n <= 23`.  Composite exponents are reduced to the
formal FLT theorems at `3`, `4`, `5`, `7`, `11`, `13`, `17`, `19`, or `23`.
The same reduction excludes a mixed-power equation whenever an integer from
`3` through `23` divides all three exponents.  This is a genuine unconditional
FLT23 milestone, but that common-divisor result alone does not prove Beal's
conjecture.

`BealRegular/SignatureReduction.lean` now proves the exact coordinatewise
normalization: every exponent greater than two is a positive multiple of `4`
or of an odd prime.  It transforms any nonzero natural-number solution into a
solution with each exponent in that reduced family, while preserving exactly
the existence of one prime dividing all three bases.  Consequently Lean proves
that Beal's conjecture is logically equivalent to its restriction to reduced
signatures.  This is a reduction, not a proof of the conjecture: the infinite
mixed families such as `(4, 5, 23)` and `(3, 7, 11)` remain to be settled.

`BealRegular/GaussianCubeParametrization.lean` starts the reduced signature
`(4, 4, 3)`.  For coprime `x, y` with `x^4 + y^4` odd, it proves that any
equation `x^4 + y^4 = z^3` makes `x^2 + y^2 i` a Gaussian cube and derives
the resulting coprime two-parameter coordinate identities.
`BealRegular/QuarticThreeDescent.lean` independently gives an unconditional
infinite descent excluding solutions of `u^4 = 3 * v^4 + w^2` whose quartic
bases `u` and `v` are nonzero and coprime (with no nonzero assumption on `w`).
`BealRegular/GaussianQuarticThreeBridge.lean` now supplies the complete
bridge, including parity, the regular and exceptional factor-of-`3` square
splits, and both integer-sign orientations.  Lean therefore solves the
reduced `(4, 4, 3)` signature with Beal's exact conclusion: every nonzero
natural solution of `A^4 + B^4 = C^3` has one prime dividing all three bases.
This settles that signature, not the full Beal conjecture; the other mixed
reduced signatures remain open here.

`BealRegular/FourthPowerSumDivisibility.lean` extends that solved signature to
an infinite family.  If `3` divides `n`, every nonzero solution of
`A^4 + B^4 = C^n` has one prime dividing `A`, `B`, and `C`; this is Beal's
exact conclusion, not merely a primitive nonexistence statement.  If `4`
divides `n`, formal FLT4 rules out every solution with nonzero bases without a
coprimality assumption.  The combined theorem covers every nonzero-base
solution whose result exponent is divisible by `3` or `4`; it does not claim
anything about the remaining result exponents.

`BealRegular/Signature357Residues.lean` begins the smallest unresolved reduced
signature `(3, 5, 7)` with unconditional local restrictions.  Any natural
identity `A^3 + B^5 = C^7` avoids two residue classes for `C` modulo `31`, four
for `B` modulo `43`, and six for `A` modulo `71`.  These are necessary local
conditions only: they do not prove that the `(3, 5, 7)` signature has no
primitive solution, and therefore do not settle the full Beal conjecture.

`BealRegular/Signature357PrimePower.lean` adds conditional 2-adic restrictions
for pairwise-coprime `(3, 5, 7)` identities: according to which base is even,
it proves congruences modulo `8`, `32`, or `128`.  The statements allow zero
bases, do not assert that any particular branch occurs, exclude no branch,
and do not solve the `(3, 5, 7)` signature.

`BealRegular/Signature357FiveAdic.lean` treats another conditional branch.
Assuming `5 ∣ C`, `A` coprime to `C`, and `B` coprime to `C` in
`A^3 + B^5 = C^7`, it proves `A^12500 = 1` modulo `78125`, together with the
readable consequences `A^4 = 1` modulo `25` and
`A mod 25 ∈ {1, 7, 18, 24}`.  No coprimality between `A` and `B`, positivity,
or nonzero hypotheses are required.  This does not prove that the `5 ∣ C`
branch occurs or that it is impossible, and it does not solve `(3, 5, 7)`.

`BealRegular/Signature357SevenAdic.lean` treats the conditional `7 ∣ A`
branch.  Assuming `7 ∣ A` and `A^3 + B^5 = C^7`, with only `A`--`B` and
`A`--`C` coprimality, it proves `B = C^119` modulo `343`, then that `B` is a
sixth root of unity modulo `49`, with
`B mod 49 ∈ {1, 18, 19, 30, 31, 48}`.  No coprimality between `B` and `C`,
positivity, or nonzero hypotheses are required; in particular, `A = 0` is
permitted.  The theorems assume rather than derive `7 ∣ A`; they neither
exclude that branch nor solve `(3, 5, 7)`.

`BealRegular/Signature357CrossPrimeAdic.lean` treats two separate conditional
placements.  In the assumed `5 ∣ B` branch, with only `A`--`B` and `B`--`C`
coprimality, it proves `C = A^1429` modulo `3125`.  This theorem permits
`B = 0`; indeed, `(A, B, C) = (1, 0, 1)` satisfies all of its premises.  In
the separately assumed `7 ∣ C` branch, with only `A`--`C` and `B`--`C`
coprimality, it proves `B + A^423537 = 0` modulo `823543`, as well as
`B^14 = 1` modulo `49` and
`B mod 49 ∈ {1, 6, 8, 13, 15, 20, 22, 27, 29, 34, 36, 41, 43, 48}`.
Neither divisibility placement is derived or excluded, and these restrictions
do not prove that the `(3, 5, 7)` signature has no solution.

`BealRegular/Signature357RemainingPrimeBranches.lean` treats two more
conditional placements.  In the assumed `5 ∣ A` branch, with only `A`--`B`
and `A`--`C` coprimality, it proves `C = B^15` modulo `125` and
`C mod 25 ∈ {1, 7, 18, 24}`.  This branch allows the genuine zero-base case
`(A, B, C) = (0, 1, 1)`.  In the separately assumed `7 ∣ B` branch, with
only `A`--`B` and `B`--`C` coprimality, it proves `A^6 = 1` and `C^14 = 1`
modulo `49`, yielding coordinatewise necessary residue lists for `A` and
`C`.  This branch allows `(A, B, C) = (1, 0, 1)`.  The lists are necessary
conditions only; they do not assert that any listed residue pair is realized.
Neither divisibility placement is derived or excluded, and no nonexistence
result for `(3, 5, 7)` follows.

`BealRegular/Signature357CompositeLocal.lean` gives three-adic restrictions
for pairwise-coprime natural identities `A^3 + B^5 = C^7`.  Its main table
packages three implications: assuming `3 ∣ A` gives `B = C^5` modulo `27`;
assuming `3 ∣ B` gives `C = A^93` modulo `243`; and assuming `3 ∣ C` gives
`B + A^33 = 0` modulo `243`.  A second table gives corresponding `±1`
coordinate restrictions modulo `9` in the latter two branches.  The tables do
not derive any divisibility premise, are not an exhaustive branch split, and
may be entirely vacuous when no base is divisible by `3`.  Their natural-number
scope includes `(A, B, C) = (0, 1, 1)` and `(1, 0, 1)`.  No branch is derived
or excluded, and no nonexistence result for `(3, 5, 7)` follows.

`BealRegular/Signature357LocalRatio.lean` formalizes the forward local-ratio
valuation profile for positive pairwise-coprime identities
`A^3 + B^5 = C^7`.  Using the paper's variable map `x = B`, `y = A`,
`z = C`, it sets `eta = B^5/C^7` and proves
that, for every prime, the valuation pair `(v(eta), v(1-eta))` has one of the
four shapes `(0, 0)`, `(5k, 0)`, `(0, 3k)`, or `(-7k, -7k)`, with `k > 0`
in the latter three cases.  Mathlib defines `padicValRat p 0 = 0`, so the
quotient formulas carry explicit nonzero hypotheses and the main profile uses
positive bases.  This is a forward valuation statement only: it gives no
converse or local-algebra classification, proves no nonexistence result, and
does not settle the full Beal conjecture.

`BealRegular/Signature357PolynomialBridge.lean` formalizes the rational
specialization of Dahmen--Siksek's degree-seven polynomial
`phi(t) = 15t^7 - 35t^6 + 21t^5`.  It proves the exact factorizations at the
critical values `0` and `1`, the derivative identity
`phi'(t) = 105t^4(t-1)^2`, and the factorized resultant with `phi - eta`.
It then proves their discriminant formula
`disc(phi-eta) = -3^6 5^6 7^7 eta^4(eta-1)^2`, including nonvanishing when
`eta != 0, 1`.  These are rational polynomial identities suitable for later
base change.  They do not yet prove a `Q_p` local-algebra isomorphism,
ramification classification, or separability theorem, and they prove no
nonexistence result for `(3, 5, 7)` or the full Beal conjecture.

`BealRegular/Signature357GenericLocalPolynomial.lean` transports that bridge
to every characteristic-zero field and links it directly to the canonical
rational `phi`.  For every parameter `u`, it proves the same resultant and
discriminant formulas; for `u != 0, 1`, it proves polynomial separability and
squarefreeness, preserved by every field extension.  It includes the explicit
discriminant and separability statements over each p-adic field `Q_p`.  These
are polynomial and scalar-extension results only: they do not construct or
classify the quotient algebra, prove finite etaleness or ramification facts,
analyze Newton polygons, exclude a `(3, 5, 7)` solution, or settle Beal.

`BealRegular/Signature357LocalAlgebra.lean` packages the canonical quotient
`K[X]/(phi-u)`.  Every fiber has a power basis and vector-space dimension
exactly seven.  If `u != 0, 1`, the quotient is reduced, module-finite, and
etale over `K`; the same statements are exposed explicitly over every p-adic
field `Q_p`.  This algebraic-geometric etaleness statement is not the paper's
valuation-theoretic unramified classification.  The module proves no product
decomposition, structural-stability or Newton-polygon result, local
ramification classification, `(3, 5, 7)` nonexistence theorem, or full Beal
claim.

`BealRegular/Signature357BranchNormalForms.lean` names the quadratic `psi` and
quartic `Psi` factors from Dahmen--Siksek equation (8) and proves the exact
fifth-power, translated cubic, and inverse-scaled seventh-power normal forms
used before Proposition 3.3.  The identities hold over every field; the paper
uses them with `q = p^r` over `Q_p`.  They are algebraic inputs only and do not
prove structural stability, quotient-product isomorphisms, Newton-polygon or
valuation-ramification results, `(3, 5, 7)` nonexistence, or the full Beal
conjecture.

`BealRegular/Signature357ModelFactorInvariants.lean` computes the exact
degrees, discriminants, and separability of `psi`, `Psi`, and the normalized
cubic, quintic, and septic binomial factors used in the local models.  In
particular, the two critical separable factors have discriminants `-35` and
`3^3 * 5^2 * 7^3`.  The binomial results concern the displayed model
polynomials themselves: they do not identify an original fiber quotient with
a product of model quotients, prove structural stability or a Newton-polygon
theorem, classify valuation ramification, exclude `(3, 5, 7)`, or prove Beal.

`BealRegular/Signature357ModelFactorAlgebras.lean` packages the `psi`, `Psi`,
and normalized binomial quotients.  The fixed quotients have dimensions two
and four.  A positive-degree binomial quotient is module-finite with dimension
`n`; when its parameter is nonzero it is also finite etale over the coefficient
field.  This is algebraic-geometric `Algebra.Etale`: the results do not claim
that the quotients are fields, identify an original fiber quotient with their
product, prove structural stability or integral-model etaleness, or classify
valuation-theoretic ramification.

`BealRegular/Signature357PadicModelUnits.lean` realizes the same factors over
the p-adic integers.  For `p != 3, 5, 7`, the endpoint coefficients and exact
discriminants of `psi` and `Psi` have p-adic norm one; more generally, if `a`
is a unit and `p` does not divide the positive degree `n`, then the endpoints
and discriminant of `X^n - a` are units.  These statements verify the
endpoint-unit and discriminant-unit arithmetic inputs used by the local
models.  They do not deduce the rootwise derivative norm bound from the unit
discriminants, lift nearby factors, identify quotient algebras, prove
structural stability or a Newton-polygon theorem, or classify
valuation-theoretic ramification.

`BealRegular/Signature357CriticalFiberDecomposition.lean` applies the Chinese
remainder theorem at the exact critical parameters.  The `u = 0` quotient is
the product of the quadratic `psi` quotient and the `X^5` primary quotient.
After translation by one, the `u = 1` quotient is the product of the quartic
`Psi` quotient and the `X^3` primary quotient; the module also transports this
decomposition back to the original variable.  These fibers are nonreduced
critical limits.  No theorem identifies a nearby `q != 0` p-adic fiber with
these products, proves structural stability or a Newton-polygon result,
classifies valuation ramification, excludes `(3, 5, 7)`, or settles Beal.

The regular-prime results at `17` and `19` are proved here by exact cyclotomic
PID certificates, not by assuming their class numbers.  Sage was used only to
discover the integer-polynomial witnesses.  Lean checks all `103` certificates
for `17` and all `558` certificates for `19`; independent Node validators
check the generated data and dispatch tables, and the renderers are byte-
idempotent.

Exponent `23` is now unconditional through the global odd-character
factorization described below.  The earlier certificate routes remain useful
independent checks and alternatives.  In particular, the project kernel-checks
the finite Bernoulli numerator condition and proves that an exponent-three
certificate for the cyclotomic class group would imply regularity and FLT23.
`BealRegular/CubicIdealCertificate.lean` also verifies
the exact five-polynomial certificate showing that a Kummer--Dedekind ideal
has principal cube.  `BealRegular/TwentyThreePrimeTwoCube.lean` applies that
checker to a concrete irreducible degree-11 factor modulo `2`, identifies the
resulting prime ideal above `2`, and proves its cube principal.
`BealRegular/TwentyThreePrimeThreeCube.lean` checks the analogous certificate
for a prime above `3`.  Galois conjugacy makes one selected prime sufficient
for each rational prime, so these two relations finish the two degree-11
rational primes in the full-field Minkowski sieve.
`BealRegular/TwentyThreeRamifiedPrime.lean` also uses Mathlib's cyclotomic
ramification theorems to identify the unique prime above `23` as the principal
ideal generated by `zeta_23 - 1`.  A checked composition theorem fills the
one-prime-above callback at `2`, `3`, and `23`.  These results do not prove that
every class has exponent three: `28,262` degree-one and `19` degree-two
rational primes remain on that brute-force route.
`BealRegular/TwentyThreeRealSubfield.lean` begins the compact alternative: it
proves that the maximal real subfield has degree `11`, constructs
`-(zeta_23 + zeta_23^-1)` inside it, and checks that the displayed monic
degree-11 polynomial vanishes there.
`BealRegular/TwentyThreeRealSubfieldEisenstein.lean` proves the shifted
polynomial is `23`-Eisenstein, transports irreducibility back to the original
polynomial, identifies it with the minimal polynomial over `ℚ`, and proves the
explicit element generates the full real subfield.
`BealRegular/TwentyThreeRealSubfieldPowerBasis.lean` packages the original and
shifted generators as rational power bases and proves the norm-resultant bridge
needed for their discriminants.
`BealRegular/TwentyThreeRealSubfieldDiscriminant.lean` kernel-checks an exact
ten-step Euclidean resultant certificate for discriminant `23^10` and combines
it with the Eisenstein shift to prove that the generated order is the full ring
of integers.  `TwentyThreeRealSubfieldRingOfIntegers.lean` transports both
integral power bases to the canonical ring of integers, proves the field
discriminant is `23^10`, and computes the exact Minkowski floor `900`.
`TwentyThreeRealSubfieldPrimeClassification.lean` proves that every rational
prime below that cutoff either has prime-ideal norm already above the cutoff or
belongs to an exact thirteen-prime list.  The ramified prime `23` is principal,
and twelve generated `TwentyThreeRealCertificate*.lean` modules check exact
integer-polynomial certificates for the remaining primes.  Their composition
in `TwentyThreeRealSubfieldPID.lean` proves unconditionally that the maximal
real subfield is a PID and has class number one.

`TwentyThreeHasseUnitIndex.lean` proves unconditionally that the Hasse
unit index of `ℚ(ζ₂₃)` is one.  Its integral power-basis argument shows that
complex conjugation acts trivially modulo `(ζ₂₃ - 1)`; a hypothetical index of
two would then force `-1 = 1` in that residue field and hence put `2` in the
ramified prime, a contradiction.  This settles the unit-index factor used by
the analytic relative class-number calculation completed below.

`RelativeClassGroup.lean` defines the quotient of the upper class group by
classes extended from a base field, carefully calling its generic cardinality
an extended-class index rather than a relative class number.  It proves that
over the now-established class-number-one real subfield this index is exactly
the full cyclotomic class number.  `TwentyThreeRelativeClassNumberResultant.lean`
then kernel-checks an exact polynomial remainder certificate for
`Res(X^11 + 1, S) = -3 * 46^10`, where the coefficients of `S` are the powers
of the primitive residue `5` modulo `23`.  The independent Node checker reaches
the same integer by fraction-free determinant arithmetic.

`TwentyThreeOddCharacterProduct.lean` now connects that exact resultant to the
analytic special values.  It kernel-checks that the powers of `5` enumerate
the nonzero residues modulo `23`, identifies each residue-weighted character
sum with `S(chi(5))`, and proves that the eleven values `chi(5)` for odd
characters are exactly the roots of `X^11 + 1`.  Together with the
unconditional `L(chi, 0)` formula from `SinZetaOne.lean`, this proves
`prod_(chi odd) L(chi, 0) = 3 * 2^10 / 23`, or equivalently that the normalized
finite product is exactly `3`.  This closes the finite odd-character product
consumed by the global factorization below.

`TwentyThreeAnalyticClassNumber.lean` now specializes the analytic class-number
formula on both fields and cancels every known signature, torsion,
discriminant, real-subfield class-number, and CM-regulator constant.  It proves
that the explicitly scaled Dedekind-zeta residue ratio is exactly `h / Q`,
where `h` is the cyclotomic class number and `Q` is the Hasse unit index.  Since
`TwentyThreeHasseUnitIndex.lean` proves `Q = 1`, the remaining odd-character
factorization is exposed as the proposition
`OddCharacterAnalyticBridgeTwentyThree`; if supplied, Lean proves `h = 3`,
regularity of `23`, and FLT for exponent `23`.

`TwentyThreeOddCharacterAnalyticBridge.lean` sharpens that remaining boundary
to the explicitly defined proposition `GlobalFactorizationTwentyThree`: on
`Re(s) > 1`, the cyclotomic Dedekind zeta function factors as the maximal-real
subfield zeta function times the product of the eleven odd Dirichlet
`L`-series.  The module proves the primitive-character and root-number lemmas,
the individual and finite-product functional equations, and the residue-limit
argument.  Under that one proposition, positivity forces the total root
number to be `+1`, the existing analytic bridge follows, and Lean obtains
class number `3`, regularity of `23`, and FLT for exponent `23`.

`TwentyThreeRealPrimeDecomposition.lean` classifies the inertia degree and
number of primes in the maximal real subfield for every rational prime away
from `23`.  `TwentyThreeDedekindLocalFactors.lean` combines those results with
the full cyclotomic splitting calculation, proves the corresponding Dedekind
local-factor identity in all four residue-order cases, and handles the unique
ramified prime at `23`.  `TwentyThreeGlobalFactorization.lean` then assembles
the pointwise identities with the convergent Euler products on `Re(s) > 1`.
It proves `GlobalFactorizationTwentyThree` with no hypothesis, and therefore
proves cyclotomic class number `3`, regularity of `23`, and FLT23.

`TwentyThreeLocalEulerFactors.lean` proves the finite algebraic local-factor
calculation away from `23`.  It defines the eleven odd Dirichlet characters
modulo `23`, proves that a nonzero residue has order `1`, `2`, `11`, or `22`,
and computes the corresponding odd-character Euler polynomials as
`(1 - X)^11`, `(1 + X)^11`, `1 - X^11`, and `1 + X^11`.  It also proves the
matching cyclotomic/real-subfield denominator identities and applies them
directly to every rational prime `q != 23`, together with the full cyclotomic
splitting-count formula.  `TwentyThreeDedekindLocalFactors.lean` specializes
these polynomial identities to the Dedekind Euler factors and supplies the
ramified local identification at `q = 23`.

`DedekindZetaEulerFoundations.lean` identifies nonzero ideals in any Dedekind
domain with finite multisets of height-one prime ideals, proves the
corresponding norm-product and fixed-norm coefficient formulas, and proves
absolute summability of the ideal-count Dirichlet series on `Re(s) > 1`.
`MultisetEulerProduct.lean` supplies the missing analytic grouping theorem for
a free commutative monoid.  `DedekindZetaEulerProduct.lean` combines them to
prove unconditionally that, for every number field and `Re(s) > 1`,
`dedekindZeta` is the convergent product of its prime-ideal geometric factors.
It also groups those factors by the rational prime below them and identifies
each fiber with Mathlib's finite `primesOver (span {q})` type.  The specialized
modules above provide the remaining local identities.  No continuation of the
Euler product beyond its half-plane of absolute convergence is needed: the
existing analytic bridge takes the residue limit from within `Re(s) > 1`.

`OddLValueAtZero.lean` now proves unconditionally that the odd Hurwitz zeta
value at zero is `sinZeta a 1 / pi`.  Given one pointwise Fourier endpoint, it
then reduces the `L(0)` value of any odd function on `ZMod N` to its standard
finite weighted sum.  That sole input is the explicitly named proposition
`ZMod.SinZetaOneSawtoothFormula N`; it is passed as a theorem parameter and is
not installed as an axiom or instance.  `SawtoothFourier.lean` now proves the
underlying conditionally convergent series in natural order: for `0 < x < 1`,
the partial sums of `sin (2 * pi * k * x) / k` tend to
`pi * (1 / 2 - x)`.  `SinZetaOne.lean` supplies the analytic endpoint: its
generic Abelian boundary theorem identifies Mathlib's analytically continued
`HurwitzZeta.sinZeta x 1` with that natural-order limit.  It proves
`ZMod.SinZetaOneSawtoothFormula N` unconditionally for every nontrivial
modulus, and therefore gives unconditional weighted-sum formulas for odd
functions and odd Dirichlet characters at zero.  This closes the sine-zeta
endpoint.  `TwentyThreeOddCharacterProduct.lean` uses those values to compute
the finite product over all odd characters, which the completed global
factorization feeds into the class-number computation.

`TwentyThreeRelativeClassNumber.lean` retains an alternative
assumption-explicit interface, `RelativeClassNumberFormulaTwentyThree`, for an
integer-form relative class-number theorem.  The completed Euler-product route
does not assume that interface and does not claim that the non-PID cyclotomic
field is a PID.  `TwentyThreeBernoulli.md` and `TwentyThreeDesign.md` document
the earlier alternative proof programs.

The alternative Kummer route remains reduced to one explicit core:
`BernoulliPadicUnitCondition p` must imply that the cyclotomic class group has
no `p`-torsion.  The surrounding denominator, valuation, finite-group, and
Galois-action lemmas are kernel-checked here; the missing implication requires
Stickelberger/Herbrand machinery that is not currently available in Mathlib.

Useful verification commands are:

```sh
lake build BealRegular
lake env lean BealRegularAudit.lean
node scripts/validate_17_certificates.mjs
node scripts/validate_19_certificates.mjs
node scripts/validate_23_prime2_cube_certificate.mjs
node scripts/validate_23_prime3_cube_certificate.mjs
node scripts/validate_23_real_certificates.mjs
node scripts/render_23_real_certificates.mjs
node scripts/TwentyThreeRelativeClassNumber.mjs
```

The following readme has been shamelessly copied from the [Liquid Tensor Experiment](https://github.com/leanprover-community/lean-liquid/).

## How to browse this repository

### Blueprint

Here are a draft [blueprint](https://leanprover-community.github.io/flt-regular/blueprint) and  [dependency graph](https://leanprover-community.github.io/flt-regular/blueprint/dep_graph_document.html).

### Getting the project

The recommended way of browsing this repository is by using a Lean development environment.
Crucially, this will allow you to inspect Lean's "Goal state" during proofs,
and easily jump to definitions or otherwise follow paths through the code. Please use the
[installation instructions](https://leanprover-community.github.io/get_started.html#regular-install)
to install Lean and a supporting toolchain.
After that, download and open a copy of the repository
by executing the following command in a terminal:
```
git clone https://github.com/leanprover-community/flt-regular.git
cd flt-regular
lake exe cache get
lake build
code .
```
For detailed instructions on how to work with Lean projects,
see [this](https://leanprover-community.github.io/install/project.html).

You can also use gitpod and do everything directly in your browser, without installing anything.
Just click on [![Gitpod](https://img.shields.io/badge/Gitpod-ready--to--code-908a85?logo=gitpod)](https://gitpod.io/#https://github.com/leanprover-community/flt-regular), but beware that everything will be slower than on your computer.

### Reading the project

With the project opened in VScode,
you are all set to start exploring the code.
There are two pieces of functionality that help a lot when browsing through Lean code:

* "Go to definition": if you right-click on a name of a definition or lemma
  (such as `is_regular_number`, or `flt_regular_case_one`), then you can choose "Go to definition" from the menu,
  and you will be taken to the relevant location in the source files.
  This also works by `Ctrl`-clicking on the name.
* "Goal view": in the event that you would like to read a *proof*,
  you can step through the proof line-by-line,
  and see the internals of Lean's "brain" in the Goal window.
  If the Goal window is not open,
  you can open it by clicking on one of the icons in the top right hand corner.

### Organization of the project

* All the Lean code (the juicy stuff) is contained in the directory `FltRegular/`.
* The file `FltRegular/FltRegular.lean` contains the statement of Fermat's Last Theorem for
  regular primes.
* The ingredients that go into the theorem statement are defined in several other files.
  The most important pieces are:
  - `NumberTheory/RegularPrimes.lean` we give the definition of what a regular number is.
  - `NumberTheory/*` are the files we are actively working on.
  - `ReadyForMathlib/*` are the files that are (almost) ready to be PRed to mathlib.

Note that we are trying to move all our results to mathlib as fast as possible, so the
folder `ReadyForMathlib` changes rapidly. You should also check `Mathlib.NumberTheory.Cyclotomic.*`.

## Brief note on type theory

Lean is based on type theory,
which means that some things work slightly differently from set theory.
We highlight two syntactical differences.

* Firstly, the element-of relation (`∈`) plays no fundamental role.
  Instead, there is a typing judgment (`:`).

  This means that we write `x : X` to say that "`x` is a term of type `X`"
  instead of "`x` is an element of the set `X`".
  Conveniently, we can write `f : X → Y` to mean "`f` has type `X → Y`",
  in other words "`f` is a function from `X` to `Y`".

* Secondly, type theorists use lambda-notation.
  This means that we can define the square function on the integers via
  `fun x ↦ x^2`, which translates to `x ↦ x^2` in set-theoretic notation.
  For more information about `λ` (called `fun` in Lean 4), see the Wikipedia page on
  [lambda calculus](https://en.wikipedia.org/wiki/Lambda_calculus).

For a more extensive discussion of type theory,
see the dedicated
[page](https://leanprover-community.github.io/lean-perfectoid-spaces/type_theory.html)
on the perfectoid project website.

[![Gitpod ready-to-code](https://img.shields.io/badge/Gitpod-ready--to--code-908a85?logo=gitpod)](https://gitpod.io/#https://github.com/leanprover-community/flt-regular)
