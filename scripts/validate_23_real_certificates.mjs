#!/usr/bin/env node

/*
 * Independent BigInt validator for the p = 23 maximal-real-subfield corpus.
 * It does not import the renderer and uses no third-party dependencies.
 *
 * Usage:
 *   node validate_23_real_certificates.mjs [input.json] [generated-directory]
 */

import { createHash } from "node:crypto";
import { readFile, readdir } from "node:fs/promises";
import { basename, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const here = fileURLToPath(new URL(".", import.meta.url));
const inputPath = resolve(process.argv[2] ?? `${here}/certificates_23_real.json`);
const generatedDirectory = resolve(process.argv[3] ?? `${here}/../BealRegular`);
const payload = JSON.parse(await readFile(inputPath, "utf8"));

function check(condition, message) {
  if (!condition) throw new Error(message);
}

function canonicalize(value) {
  if (Array.isArray(value)) return value.map(canonicalize);
  if (value !== null && typeof value === "object") {
    return Object.fromEntries(Object.keys(value).sort().map((key) => [key, canonicalize(value[key])]));
  }
  return value;
}

function trim(polynomial) {
  const result = [...polynomial];
  while (result.length > 0 && result.at(-1) === 0n) result.pop();
  return result;
}

function polynomial(values) {
  check(Array.isArray(values), "polynomial data must be an array");
  return trim(values.map(BigInt));
}

function add(...polynomials) {
  const length = Math.max(0, ...polynomials.map((entry) => entry.length));
  return trim(Array.from({ length }, (_, index) =>
    polynomials.reduce((sum, entry) => sum + (entry[index] ?? 0n), 0n)));
}

function scale(scalar, entry) {
  return trim(entry.map((coefficient) => scalar * coefficient));
}

function multiply(left, right) {
  if (left.length === 0 || right.length === 0) return [];
  const result = Array(left.length + right.length - 1).fill(0n);
  for (let i = 0; i < left.length; i += 1) {
    for (let j = 0; j < right.length; j += 1) result[i + j] += left[i] * right[j];
  }
  return trim(result);
}

function equal(left, right) {
  const a = trim(left);
  const b = trim(right);
  return a.length === b.length && a.every((coefficient, index) => coefficient === b[index]);
}

function absolute(value) {
  return value < 0n ? -value : value;
}

function isPrime(value) {
  if (!Number.isSafeInteger(value) || value < 2) return false;
  if (value % 2 === 0) return value === 2;
  for (let divisor = 3; divisor * divisor <= value; divisor += 2) {
    if (value % divisor === 0) return false;
  }
  return true;
}

function evaluateMod(entry, value, modulus) {
  let result = 0n;
  for (let index = entry.length - 1; index >= 0; index -= 1) {
    result = (result * value + entry[index]) % modulus;
  }
  return (result + modulus) % modulus;
}

function divRemMonic(numerator, divisorInput) {
  const remainder = trim(numerator);
  const divisor = trim(divisorInput);
  check(divisor.length > 0 && divisor.at(-1) === 1n, "monic divisor required");
  const quotient = Array(Math.max(0, remainder.length - divisor.length + 1)).fill(0n);
  while (remainder.length >= divisor.length) {
    const shift = remainder.length - divisor.length;
    const coefficient = remainder.at(-1);
    quotient[shift] = coefficient;
    for (let index = 0; index < divisor.length; index += 1) {
      remainder[index + shift] -= coefficient * divisor[index];
    }
    while (remainder.length > 0 && remainder.at(-1) === 0n) remainder.pop();
  }
  return [trim(quotient), remainder];
}

function determinantBareiss(matrix) {
  check(matrix.length > 0 && matrix.every((row) => row.length === matrix.length),
    "Bareiss matrix must be nonempty and square");
  const work = matrix.map((row) => [...row]);
  let sign = 1n;
  let previousPivot = 1n;
  for (let pivotIndex = 0; pivotIndex < work.length - 1; pivotIndex += 1) {
    let pivotRow = pivotIndex;
    while (pivotRow < work.length && work[pivotRow][pivotIndex] === 0n) pivotRow += 1;
    if (pivotRow === work.length) return 0n;
    if (pivotRow !== pivotIndex) {
      [work[pivotRow], work[pivotIndex]] = [work[pivotIndex], work[pivotRow]];
      sign = -sign;
    }
    const pivot = work[pivotIndex][pivotIndex];
    for (let row = pivotIndex + 1; row < work.length; row += 1) {
      for (let column = pivotIndex + 1; column < work.length; column += 1) {
        const numerator = work[row][column] * pivot -
          work[row][pivotIndex] * work[pivotIndex][column];
        check(numerator % previousPivot === 0n, "non-exact Bareiss division");
        work[row][column] = numerator / previousPivot;
      }
    }
    previousPivot = pivot;
  }
  return sign * work.at(-1).at(-1);
}

function multiplicationNorm(definingPolynomial, element) {
  const degree = definingPolynomial.length - 1;
  const matrix = Array.from({ length: degree }, () => Array(degree).fill(0n));
  for (let column = 0; column < degree; column += 1) {
    const shifted = Array(column).fill(0n).concat(element);
    const [, remainder] = divRemMonic(shifted, definingPolynomial);
    for (let row = 0; row < degree; row += 1) matrix[row][column] = remainder[row] ?? 0n;
  }
  return determinantBareiss(matrix);
}

const expectedPolynomial = [1n, -6n, -15n, 35n, 35n, -56n, -28n, 36n, 9n, -10n, -1n, 1n];
const definingPolynomial = polynomial(payload.polynomial);
check(equal(definingPolynomial, expectedPolynomial), "unexpected defining polynomial");
check(payload.field_discriminant === (23n ** 10n).toString(), "unexpected field discriminant metadata");
check(payload.class_number === "1", "unexpected Sage class-number metadata");
check(Array.isArray(payload.certificates), "certificates must be an array");

const expectedPrimes = [];
for (let candidate = 2; candidate <= 900; candidate += 1) {
  if (!isPrime(candidate) || candidate === 23) continue;
  const residue = candidate % 23;
  if (residue === 1 || residue === 22) expectedPrimes.push(candidate);
}
const serializedPrimes = payload.certificates.map(({ q }) => q);
check(JSON.stringify(serializedPrimes) === JSON.stringify(expectedPrimes),
  "certificate primes are not exactly the split primes in the Minkowski interval");
check(new Set(serializedPrimes).size === serializedPrimes.length, "duplicate certificate prime");

const derivative = definingPolynomial.slice(1).map((coefficient, index) =>
  BigInt(index + 1) * coefficient);
const derivativeNorm = multiplicationNorm(definingPolynomial, derivative);
const degree = definingPolynomial.length - 1;
const discriminant = ((degree * (degree - 1) / 2) % 2 === 0 ? 1n : -1n) * derivativeNorm;
check(discriminant === 23n ** 10n, `computed discriminant ${discriminant} is not 23^10`);

const polynomialNames = ["P", "Q", "A", "G", "Qq", "Rq", "QP", "RP", "C1", "C2"];
for (const certificate of payload.certificates) {
  const q = BigInt(certificate.q);
  check(isPrime(certificate.q), `${certificate.q}: q is not prime`);
  check(certificate.q <= 900, `${certificate.q}: q exceeds the Minkowski floor`);
  check(certificate.q % 23 === 1 || certificate.q % 23 === 22,
    `${certificate.q}: q is not split completely in the real field`);

  const entries = Object.fromEntries(polynomialNames.map((name) =>
    [name, polynomial(certificate[name])]));
  const { P, Q, A, G, Qq, Rq, QP, RP, C1, C2 } = entries;
  check(P.length === 2 && P[1] === 1n, `${certificate.q}: P is not monic linear`);
  const root = ((-P[0]) % q + q) % q;
  check(evaluateMod(definingPolynomial, root, q) === 0n,
    `${certificate.q}: P does not divide f modulo q`);

  check(equal(definingPolynomial, add(multiply(P, Q), scale(q, A))),
    `${certificate.q}: f = P*Q + q*A failed`);
  check(equal([q], add(multiply(G, Qq), multiply(definingPolynomial, Rq))),
    `${certificate.q}: q = G*Qq + f*Rq failed`);
  check(equal(P, add(multiply(G, QP), multiply(definingPolynomial, RP))),
    `${certificate.q}: P = G*QP + f*RP failed`);
  check(equal(G, add(multiply(C1, P), scale(q, C2))),
    `${certificate.q}: G = C1*P + q*C2 failed`);

  const norm = multiplicationNorm(definingPolynomial, G);
  check(norm === BigInt(certificate.norm),
    `${certificate.q}: computed norm ${norm} != ${certificate.norm}`);
  check(norm === BigInt(certificate.resultant_f_G),
    `${certificate.q}: resultant metadata differs from computed norm`);
  check(absolute(norm) === q, `${certificate.q}: generator norm is not +/-q`);

  const score = polynomialNames.reduce((maximum, name) =>
    entries[name].reduce((inner, coefficient) =>
      absolute(coefficient) > inner ? absolute(coefficient) : inner, maximum), 0n);
  check(score.toString() === certificate.score, `${certificate.q}: optimization score mismatch`);
}

const sortedCertificates = [...payload.certificates].sort((left, right) => left.q - right.q);
const canonicalJson = `${JSON.stringify(canonicalize({ ...payload, certificates: sortedCertificates }), null, 2)}\n`;
const digest = createHash("sha256").update(canonicalJson).digest("hex");
const expectedGenerated = new Set([
  "TwentyThreeRealCertificateBase.lean",
  "TwentyThreeRealCertificates.lean",
  "TwentyThreeRealCertificatesAudit.lean",
  ...expectedPrimes.map((q) => `TwentyThreeRealCertificate${q}.lean`),
]);
const generatedEntries = (await readdir(generatedDirectory))
  .filter((name) => /^TwentyThreeRealCertificate.*\.lean$/.test(name));
check(generatedEntries.length === expectedGenerated.size &&
  generatedEntries.every((name) => expectedGenerated.has(name)),
"generated Lean module set is incomplete or stale");

const sourceName = basename(inputPath);
for (const file of expectedGenerated) {
  const source = await readFile(resolve(generatedDirectory, file), "utf8");
  check(source.includes(`\`${sourceName}\``), `${file}: missing corpus filename header`);
  check(source.includes(digest), `${file}: corpus digest mismatch`);
  check(!/\b(sorry|admit|axiom|native_decide)\b/.test(source), `${file}: forbidden proof escape hatch`);
}
for (const q of expectedPrimes) {
  const source = await readFile(resolve(generatedDirectory, `TwentyThreeRealCertificate${q}.lean`), "utf8");
  check(source.includes(`namespace BealRegular.TwentyThreeRealCertificates.Q${q}`),
    `${q}: wrong generated namespace`);
  for (const theorem of ["factorization_identity", "principal_identities",
    "map_P_mem_monicFactorsMod", "selectedPrime_isPrincipal", "minkowski_branch"]) {
    check(source.includes(`theorem ${theorem}`), `${q}: missing theorem ${theorem}`);
  }
}

console.log(JSON.stringify({
  certificates: payload.certificates.length,
  identities: payload.certificates.length * 4,
  generatedLeanFiles: expectedGenerated.size,
  corpusSha256: digest,
  discriminant: discriminant.toString(),
  firstPrime: expectedPrimes[0],
  lastPrime: expectedPrimes.at(-1),
}));
