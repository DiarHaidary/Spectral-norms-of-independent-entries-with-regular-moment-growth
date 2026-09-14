"""Bounded exact checks of the positive-polynomial moment interface.

This does not certify a universal strong/weak theorem, a hypercontractive
theorem, the count-map theorem, the full MI-32 theorem, or any quantile claim.
All computed numbers are fractions; no random sampling or eigensolver is used.
"""

from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib
import json


BASE = Path(__file__).resolve().parent
PROOF = BASE / "regular_law_positive_cone.md"
ARCHIVED = BASE.parent / "mi32_exchange_2026-09-13" / "regular_law_operator.md"
N = 4
ZERO = (0,) * N
COUNTS = Counter()


def check(kind, condition, label):
    if not condition:
        raise AssertionError(label)
    COUNTS[kind] += 1


def clean(poly):
    return {nu: Q(c) for nu, c in poly.items() if c}


def add(*polys):
    ans = defaultdict(Q)
    for poly in polys:
        for nu, c in poly.items():
            ans[nu] += c
    return clean(ans)


def mul(a, b):
    ans = defaultdict(Q)
    for nu, c in a.items():
        for mu, d in b.items():
            ans[tuple(x + y for x, y in zip(nu, mu))] += c * d
    return clean(ans)


def scale(poly, c):
    return clean({nu: c * val for nu, val in poly.items()})


def atom(exponents, c=1):
    return {tuple(exponents): Q(c)}


def variable(i):
    nu = [0] * N
    nu[i] = 1
    return atom(nu)


def evaluate(poly, values):
    ans = Q(0)
    for nu, c in poly.items():
        val = c
        for x, power in zip(values, nu):
            val *= x ** power
        ans += val
    return ans


def degree(vector):
    return max((sum(nu) for poly in vector for nu in poly), default=0)


def parity(nu):
    return tuple(v % 2 for v in nu)


def parity_parts(vector):
    parts = {}
    for coord, poly in enumerate(vector):
        for nu, c in poly.items():
            tag = parity(nu)
            if tag not in parts:
                parts[tag] = [{} for _ in vector]
            parts[tag][coord][nu] = c
    return parts


def norm_square(vector):
    return add(*(mul(poly, poly) for poly in vector))


def joint_states(laws):
    for choices in product(*(list(law.items()) for law in laws)):
        values, probabilities = zip(*choices)
        weight = Q(1)
        for probability in probabilities:
            weight *= probability
        yield values, weight


# Each Z is bounded and max(Z) <= 2 E Z. Therefore each symmetric sign-times-Z
# law is 2-regular at ALL real orders >=1 by Jensen and monotonicity. The finite
# doubled-moment checks below are checks, not the proof of all-order regularity.
MAGNITUDES = [
    {Q(0): Q(1, 4), Q(1): Q(1, 2), Q(2): Q(1, 4)},
    {Q(1): Q(3, 4), Q(3): Q(1, 4)},
    {Q(1, 2): Q(1, 3), Q(2): Q(2, 3)},
    {Q(2): Q(1)},
]
ALPHA = Q(2)
MOMENTS = {}


def moment(edge, exponent, signed=False):
    if signed and exponent % 2:
        return Q(0)
    key = edge, exponent
    if key not in MOMENTS:
        MOMENTS[key] = sum((prob * z ** exponent
                            for z, prob in MAGNITUDES[edge].items()), Q(0))
    return MOMENTS[key]


def expect(poly, signed=False):
    ans = Q(0)
    for nu, c in poly.items():
        val = c
        for edge, exponent in enumerate(nu):
            val *= moment(edge, exponent, signed=signed)
        ans += val
    return ans


def full_signed_law(magnitudes):
    ans = defaultdict(Q)
    for z, weight in magnitudes.items():
        ans[z] += weight / 2
        ans[-z] += weight / 2
    return dict(ans)


SIGNED_LAWS = [full_signed_law(law) for law in MAGNITUDES]
MAG_STATES = list(joint_states(MAGNITUDES))
SIGNED_STATES = list(joint_states(SIGNED_LAWS))
SIGNS = list(product((-1, 1), repeat=N))


def check_cone_case(name, vector):
    d = degree(vector)
    check("cone_eligibility", all(c >= 0 for poly in vector for c in poly.values()), name)
    parts = parity_parts(vector)
    parity_degree = max((sum(tag) for tag in parts), default=0)
    check("degree", parity_degree <= d, name)
    g = add(*(norm_square(part) for part in parts.values()))
    check("cone_eligibility", all(c >= 0 for c in g.values()), name + " G positivity")
    check("degree", degree([g]) <= 2 * d, name + " G degree")
    check("parity_identity", all(not any(parity(nu)) for nu in g), name + " G even")

    total2 = total4 = amplitude_g2 = Q(0)
    for z, weight in MAG_STATES:
        coeff = {tag: [evaluate(poly, z) for poly in part]
                 for tag, part in parts.items()}
        gram = sum((x * x for values in coeff.values() for x in values), Q(0))
        check("parity_identity", gram == evaluate(g, z), name + " G evaluation")
        conditional2 = conditional4 = Q(0)
        for signs in SIGNS:
            signed_values = tuple(eps * value for eps, value in zip(signs, z))
            original = [evaluate(poly, signed_values) for poly in vector]
            restored = [Q(0) for _ in vector]
            for tag, values in coeff.items():
                eps_s = 1
                for eps, bit in zip(signs, tag):
                    eps_s *= eps ** bit
                for coord, value in enumerate(values):
                    restored[coord] += eps_s * value
            check("parity_identity", restored == original, name + " actual original reconstruction")
            squared = sum((value * value for value in original), Q(0))
            conditional2 += squared / len(SIGNS)
            conditional4 += squared * squared / len(SIGNS)
        check("conditional_second", conditional2 == gram, name)
        check("conditional_fourth_bound", conditional4 <= 9 ** parity_degree * gram * gram, name)
        total2 += weight * conditional2
        total4 += weight * conditional4
        amplitude_g2 += weight * gram * gram

    original_norm2 = norm_square(vector)
    check("joint_moment_identity", total2 == expect(original_norm2, signed=True), name + " second")
    check("joint_moment_identity", total4 == expect(mul(original_norm2, original_norm2), signed=True), name + " fourth")
    check("joint_moment_identity", total2 == expect(g), name + " EG")
    check("joint_moment_identity", amplitude_g2 == expect(mul(g, g)), name + " EG squared")
    # Independent direct enumeration of the original signed laws, including one
    # zero atom, checks the enlarged sign/amplitude probability accounting.
    enum2 = enum4 = Q(0)
    for values, weight in SIGNED_STATES:
        squared = sum((evaluate(poly, values) ** 2 for poly in vector), Q(0))
        enum2 += weight * squared
        enum4 += weight * squared * squared
    check("original_law_enumeration", enum2 == total2 and enum4 == total4, name)
    check("amplitude_moment_bound", amplitude_g2 <= ALPHA ** (8 * d) * total2 ** 2, name)
    check("positive_cone_fourth_bound", total4 <= 9 ** d * ALPHA ** (8 * d) * total2 ** 2, name)
    return {"name": name, "degree": d, "parity_degree": parity_degree,
            "coordinates": len(vector), "original_terms": sum(map(len, vector)),
            "second_moment": str(total2), "fourth_moment": str(total4),
            "EG_squared": str(amplitude_g2)}


def matrix_vacuum_cases():
    # The ORIGINAL four variables are a 2-by-2 matrix, edges (0,0),(0,1),
    # (1,0),(1,1). Matrix current vertices are rows 0,1 and columns 2,3.
    adjacency = defaultdict(list)
    for edge, (row, col) in enumerate(((0, 0), (0, 1), (1, 0), (1, 1))):
        adjacency[row].append((2 + col, edge))
        adjacency[2 + col].append((row, edge))
    cases = []
    for root in range(4):
        vector = [{} for _ in range(4)]
        vector[root] = atom(ZERO)
        for length in range(5):
            cases.append((f"original_K22_root{root}_length{length}", vector))
            nxt = [{} for _ in range(4)]
            for vertex, poly in enumerate(vector):
                for target, edge in adjacency[vertex]:
                    nxt[target] = add(nxt[target], mul(poly, variable(edge)))
            vector = nxt
    return cases


def check_variance_and_weak_second():
    variances = [moment(edge, 2) for edge in range(4)]
    max_variance = max(variances)
    rows = [sum(variances[2 * i:2 * i + 2]) for i in range(2)]
    cols = [variances[j] + variances[j + 2] for j in range(2)]
    vectors = [(Q(1), Q(0)), (Q(0), Q(1)), (Q(3, 5), Q(4, 5)),
               (Q(-3, 5), Q(4, 5)), (Q(1, 3), Q(-2, 3))]
    for s in vectors:
        snorm2 = sum(x*x for x in s)
        row_vector = [add(*(scale(variable(2*i+j), s[i]) for i in range(2))) for j in range(2)]
        exact_row_energy = expect(norm_square(row_vector), signed=True)
        check("hilbert_variance_identity", exact_row_energy == sum(s[i]**2 * rows[i] for i in range(2)), "row Hilbert second")
        check("hilbert_variance_bound", exact_row_energy <= max(rows) * snorm2, "row sigma")
        col_vector = [add(*(scale(variable(2*i+j), s[j]) for j in range(2))) for i in range(2)]
        exact_col_energy = expect(norm_square(col_vector), signed=True)
        check("hilbert_variance_identity", exact_col_energy == sum(s[j]**2 * cols[j] for j in range(2)), "col Hilbert second")
        check("hilbert_variance_bound", exact_col_energy <= max(cols) * snorm2, "column sigma")
        for t in vectors:
            scalar = add(*(scale(variable(2*i+j), s[i] * t[j]) for i in range(2) for j in range(2)))
            exact = expect(mul(scalar, scalar), signed=True)
            formula = sum(variances[2*i+j] * s[i]**2 * t[j]**2 for i in range(2) for j in range(2))
            check("weak_second_identity", exact == formula, "bilinear variance")
            check("weak_second_upper", exact <= max_variance * snorm2 * sum(x*x for x in t), "weak R2 upper")
    edge = variances.index(max_variance)
    witness = variable(edge)
    check("weak_second_attainment", expect(mul(witness, witness), signed=True) == max_variance, "coordinate attains R2")
    return {"entry_variances": list(map(str, variances)), "sigma_row_squared": str(max(rows)),
            "sigma_column_squared": str(max(cols)), "weak_R2_squared": str(max_variance),
            "coordinate_witness_edge": edge, "tested_rational_vectors": len(vectors),
            "scope": "Exact weak R2 identity follows from the displayed positive formula and coordinate attainment; higher-order weak suprema are not computed."}


def signed_indicator_control():
    # Archived all-real-order 64-regular law, L=11. The interpolation polynomial
    # is the unnormalized indicator of its positive extreme atom R=2048.
    # Its coefficients have both signs. This is an actual counterexample to
    # extending the displayed H_alpha^d cone bound to arbitrary coefficients.
    level = 11
    extreme = 2 ** level
    alpha = 64
    support = [sgn * 2 ** j for j in range(level + 1) for sgn in (-1, 1)]
    polynomial = {0: Q(1)}
    for x in support:
        if x == extreme:
            continue
        nxt = defaultdict(Q)
        for exponent, coeff in polynomial.items():
            nxt[exponent + 1] += coeff / (extreme - x)
            nxt[exponent] -= x * coeff / (extreme - x)
        polynomial = {nu: c for nu, c in nxt.items() if c}
    for x in support:
        value = sum((c * x ** nu for nu, c in polynomial.items()), Q(0))
        check("signed_indicator_interpolation", value == int(x == extreme), str(x))
    d = max(polynomial)
    eta = Q(1, 2 ** (extreme + 1))
    check("negative_control", any(c < 0 for c in polynomial.values()) and any(c > 0 for c in polynomial.values()), "outside positive cone")
    # E f^2=E f^4=eta. The fourth-power version of (5) would read:
    proposed = 9 ** d * alpha ** (8 * d) * eta ** 2
    check("negative_control", eta > proposed, "signed coefficient extension fails")
    return {"archived_law_L": level, "alpha_from_archived_analytic_proof": alpha,
            "degree": d, "positive_extreme": extreme, "extreme_probability": f"2^-{extreme+1}",
            "second_and_fourth_moment": f"2^-{extreme+1}",
            "violation_test": f"2^{extreme+1} > 9^{d} * 64^{8*d}",
            "scope": "Finite exact interpolation and violation, using the archived analytic all-real-order regularity proof. Not a finite certification of that regularity theorem."}


def main():
    for edge, law in enumerate(MAGNITUDES):
        check("law_normalization", sum(law.values()) == 1 and all(x >= 0 and w > 0 for x, w in law.items()), str(edge))
        check("all_order_regularity_certificate", max(law) <= ALPHA * moment(edge, 1), str(edge))
        for p in range(1, 13):
            check("sampled_doubling_moment", moment(edge, 2*p) <= ALPHA ** (2*p) * moment(edge, p) ** 2, str((edge,p)))
        for u in range(13):
            for v in range(13):
                check("original_moment_pair_bound", moment(edge, u+v) <= ALPHA ** (2*(u+v)) * moment(edge,u) * moment(edge,v), str((edge,u,v)))

    x = [variable(i) for i in range(N)]
    one = atom(ZERO)
    cases = [
        ("inhomogeneous_linear", [add(one, x[0], scale(x[1], 2)), add(x[2], scale(x[3], 3))]),
        ("even_magnitude_spectators", [add(x[0], mul(x[0], mul(x[2], x[2])), scale(mul(mul(x[0], x[0]), x[0]), 2)),
                                         add(one, mul(x[1], x[3]), mul(mul(x[3], x[3]), mul(x[2], x[2])))]),
        ("mixed_parity_and_constant", [add(one, mul(x[0], x[1]), mul(x[2], x[2])),
                                       add(x[1], mul(mul(x[0], x[0]), x[3]), scale(mul(x[1], x[1]), Q(3,2)))]),
    ] + matrix_vacuum_cases()
    summaries = [check_cone_case(name, vector) for name, vector in cases]
    variance = check_variance_and_weak_second()
    control = signed_indicator_control()
    report = {
        "status": "PASS", "arithmetic": "fractions.Fraction, exact; no numerical checks",
        "proof_sha256": hashlib.sha256(PROOF.read_bytes()).hexdigest(),
        "verifier_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "archived_negative_control_source": str(ARCHIVED),
        "archived_negative_control_sha256": hashlib.sha256(ARCHIVED.read_bytes()).hexdigest(),
        "counts": dict(sorted(COUNTS.items())), "total_exact_assertions": sum(COUNTS.values()),
        "positive_cases": summaries, "positive_case_count": len(summaries),
        "magnitude_laws": [{str(x): str(w) for x,w in law.items()} for law in MAGNITUDES],
        "common_alpha": str(ALPHA), "amplitude_states_per_case": len(MAG_STATES),
        "original_signed_states_per_case": len(SIGNED_STATES),
        "independent_sign_assignments_per_amplitude": len(SIGNS),
        "moment_pair_exponents": "u,v=0,...,12 on each of four original laws",
        "variance_weak_second": variance, "signed_coefficient_negative_control": control,
        "scope": [
            "Finite original-law moment identities and positive-cone inequalities, including zero amplitudes and repeated powers.",
            "Actual K_(2,2) vacuum polynomials at four roots and lengths 0,...,4; all coefficient multiplications retain original edge identities.",
            "The parity count-map compression is covered by a separate verifier, not certified here.",
            "The universal cone theorem, strong/weak theorem, thin-matrix net argument, and MI-32 endpoint require analytic proofs and independent review.",
            "No unknown universal constant is numerically estimated, no higher-order weak supremum optimized, and no matching-quantile claim made."
        ],
    }
    destination = BASE / "positive_cone_checks.json"
    destination.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "total_exact_assertions": report["total_exact_assertions"],
                      "positive_cases": len(summaries), "negative_controls": COUNTS["negative_control"],
                      "report": str(destination)}, indent=2))


if __name__ == "__main__":
    main()
