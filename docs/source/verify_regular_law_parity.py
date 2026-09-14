"""Exact bounded checks of the original parity/magnitude positive-cone interface.

No joint magnitude-law enumeration, floating point, or cutoff Jacobi basis is used.
The analytic theorem and moment assumptions are NOT proved by these finite checks.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
N = 3
EDGES = tuple(product(range(N), repeat=2))
M = len(EDGES)
ZERO = (0,) * M
COUNTS = Counter()


def clean(p):
    return {key: value for key, value in p.items() if value}


def p_add(*ps):
    out = defaultdict(F)
    for p in ps:
        for nu, a in p.items():
            out[nu] += a
    return clean(out)


def p_scale(p, a):
    return clean({nu: a * b for nu, b in p.items()})


def p_mul(p, q):
    out = defaultdict(F)
    for nu, a in p.items():
        for mu, b in q.items():
            out[tuple(x + y for x, y in zip(nu, mu))] += a * b
    return clean(out)


def raise_exp(nu, edge):
    result = list(nu)
    result[edge] += 1
    return tuple(result)


def parity(nu):
    return sum((n % 2) << e for e, n in enumerate(nu))


def counts(mask, axis):
    out = [0] * N
    for e, pair in enumerate(EDGES):
        if mask >> e & 1:
            out[pair[axis]] += 1
    return tuple(out)


def increment(d, at):
    out = list(d)
    out[at] += 1
    return tuple(out)


def direction(v):
    return 0 if v < N else 1


def endpoint(e, side):
    return EDGES[e][side] + (N if side else 0)


def other_vertex(v, e):
    a, b = EDGES[e]
    if v == a:
        return N + b
    if v == N + b:
        return a
    return None


def direct_step(vector, weights):
    """Ordinary matrix-polynomial multiplication; no flags or count labels."""
    out = defaultdict(F)
    for (v, nu), coefficient in vector.items():
        for e, weight in enumerate(weights):
            w = other_vertex(v, e)
            if w is not None:
                out[w, raise_exp(nu, e)] += coefficient * weight
    return clean(out)


def parity_step(vector, weights, branch=None):
    """Actual toggling: both branches multiply by the same original magnitude."""
    out = defaultdict(F)
    for (v, mask, nu), coefficient in vector.items():
        for e, weight in enumerate(weights):
            w = other_vertex(v, e)
            if w is None:
                continue
            occupied = bool(mask >> e & 1)
            if branch == "+" and occupied:
                continue
            if branch == "-" and not occupied:
                continue
            out[w, mask ^ (1 << e), raise_exp(nu, e)] += coefficient * weight
    return clean(out)


def lift(vector):
    return {(v, parity(nu), nu): a for (v, nu), a in vector.items()}


def unlabeled(vector):
    out = defaultdict(F)
    for (v, mask, nu), a in vector.items():
        assert parity(nu) == mask
        out[v, nu] += a
    return clean(out)


def domain_label(v, mask, branch):
    side = direction(v)
    if branch == "+":
        return increment(counts(mask, side), v % N)
    return counts(mask, 1 - side)


def range_label(v, mask, branch):
    side = direction(v)
    if branch == "+":
        return counts(mask, 1 - side)
    return increment(counts(mask, side), v % N)


def exponent_vectors(length, maximum):
    if length == 0:
        yield ()
    else:
        for head in range(maximum + 1):
            for tail in exponent_vectors(length - 1, maximum - head):
                yield (head,) + tail


def compressed_matrix_step(vector, weights, side, branch, grade, label):
    """Independently multiply the selected ORIGINAL submatrix, then project.

    This deliberately does not use an occupied-edge branch test.  Its entire
    exponent tuple is retained, including variables outside the selected axis.
    """
    active = {i for i, d in enumerate(label) if d}
    axis = side if branch == "+" else 1 - side
    ordinary_input = unlabeled(vector)
    ordinary_output = defaultdict(F)
    for e, (row, col) in enumerate(EDGES):
        if (row, col)[axis] not in active:
            continue
        vin, vout = endpoint(e, side), endpoint(e, 1 - side)
        for (v, nu), a in ordinary_input.items():
            if v == vin:
                ordinary_output[vout, raise_exp(nu, e)] += a * weights[e]
    answer = {}
    target_grade = grade + (1 if branch == "+" else -1)
    for (v, nu), a in clean(ordinary_output).items():
        mask = parity(nu)
        if mask.bit_count() == target_grade and range_label(v, mask, branch) == label:
            answer[v, mask, nu] = a
    return answer


def check_count_blocks(weights):
    # All original monomials of degree <=3 at every one of six current vertices.
    exponents = list(exponent_vectors(M, 3))
    assert len(exponents) == 220
    fixtures = {(v, parity(nu), nu): F(1 + (v + sum(nu)) % 3, 2)
                for v in range(2 * N) for nu in exponents}
    for branch in ("+", "-"):
        sectors = defaultdict(dict)
        for state, coefficient in fixtures.items():
            v, mask, nu = state
            label = domain_label(v, mask, branch)
            key = direction(v), mask.bit_count(), label
            sectors[key][state] = coefficient
        seen_inputs, seen_outputs = set(), {}
        aggregate = defaultdict(F)
        for (side, grade, label), f in sectors.items():
            active = {i for i, d in enumerate(label) if d}
            assert len(active) <= grade + (1 if branch == "+" else 0)
            COUNTS["active_axis_size_checks"] += 1
            axis = side if branch == "+" else 1 - side
            for v, mask, nu in f:
                assert (v, mask, nu) not in seen_inputs
                seen_inputs.add((v, mask, nu))
                assert all(EDGES[e][axis] in active for e in range(M) if mask >> e & 1)
                if branch == "+":
                    assert v % N in active
                # Directly check every allowed edge, including transitions that
                # subsequently cancel under signed deterministic coefficients.
                for e in range(M):
                    w = other_vertex(v, e)
                    if w is None or bool(mask >> e & 1) != (branch == "-"):
                        continue
                    outmask = mask ^ (1 << e)
                    assert range_label(w, outmask, branch) == label
                    if branch == "-":
                        assert w % N in active
                    key_out = w, outmask
                    old = seen_outputs.setdefault(key_out, (side, grade, label))
                    assert old == (side, grade, label)
                    COUNTS["individual_transition_count_invariants"] += 1
            actual = parity_step(f, weights, branch)
            projected = compressed_matrix_step(f, weights, side, branch, grade, label)
            assert actual == projected
            COUNTS["exact_submatrix_compression_equalities"] += 1
            for state, coefficient in actual.items():
                aggregate[state] += coefficient
        assert seen_inputs == set(fixtures)
        assert clean(aggregate) == parity_step(fixtures, weights, branch)
        COUNTS["orthogonal_sector_partition_equalities"] += 1


def check_even_spectators(weights):
    nu = (1, 0, 0, 0, 0, 0, 0, 0, 2)
    inp = {(0, 1, nu): F(1)}  # Current row 0, flag 00; magnitude spectator 22^2.
    for branch in ("+", "-"):
        label = domain_label(0, 1, branch)
        assert label == (1 + (branch == "+"), 0, 0)
        actual = parity_step(inp, weights, branch)
        projected = compressed_matrix_step(inp, weights, 0, branch, 1, label)
        assert actual == projected and actual
        assert all(exponent[8] == 2 and sum(exponent) == 4
                   for _, _, exponent in actual)
        assert all(parity(exponent) == mask for _, mask, exponent in actual)
        COUNTS["even_spectator_retention_checks"] += 1
    # The annihilation amplitude contains W00^2 W22^2, not a constant/first power.
    annihilated = unlabeled(parity_step(inp, weights, "-"))
    expected_nu = (2, 0, 0, 0, 0, 0, 0, 0, 2)
    assert annihilated == {(N, expected_nu): weights[0]}
    COUNTS["annihilation_multiplicity_checks"] += 1


def vector_norm_square(vector, dimension):
    polys = [dict() for _ in range(dimension)]
    for (v, nu), a in vector.items():
        polys[v][nu] = a
    return p_add(*(p_mul(p, p) for p in polys))


def matrix_poly_multiply(a, b):
    return [[p_add(*(p_mul(a[i][k], b[k][j]) for k in range(len(b))))
             for j in range(len(b[0]))] for i in range(len(a))]


def trace_yy_powers(weights, horizon):
    y = [[{} for _ in range(N)] for _ in range(N)]
    for e, (i, j) in enumerate(EDGES):
        y[i][j] = {raise_exp(ZERO, e): weights[e]}
    yt = [[y[j][i] for j in range(N)] for i in range(N)]
    yy = matrix_poly_multiply(y, yt)
    power = [[{ZERO: F(i == j)} if i == j else {} for j in range(N)]
             for i in range(N)]
    traces = {}
    for q in range(1, horizon + 1):
        power = matrix_poly_multiply(power, yy)
        traces[q] = p_add(*(power[i][i] for i in range(N)))
    return traces


def check_vacuum(weights):
    trace_rhs = trace_yy_powers(weights, 4)
    all_norms = defaultdict(list)
    signmask = sum((w < 0) << e for e, w in enumerate(weights))
    positive = tuple(abs(w) for w in weights)
    for root in range(2 * N):
        direct = {(root, ZERO): F(1)}
        flags = lift(direct)
        unsigned = lift(direct)
        for q in range(5):
            assert flags == lift(direct)
            assert all(sum(nu) == q and parity(nu) == mask
                       for _, mask, nu in flags)
            assert all(a > 0 for a in unsigned.values())
            gauged = {state: a * (-1 if (state[1] & signmask).bit_count() % 2 else 1)
                      for state, a in unsigned.items()}
            assert gauged == flags
            COUNTS["vacuum_direct_polynomial_equalities"] += 1
            COUNTS["signed_to_positive_original_sign_gauge_equalities"] += 1
            if q:
                all_norms[q].append(vector_norm_square(direct, 2 * N))
            if q == 4:
                break
            direct = direct_step(direct, weights)
            plus, minus = parity_step(flags, weights, "+"), parity_step(flags, weights, "-")
            combined = defaultdict(F, plus)
            for state, a in minus.items():
                combined[state] += a
            flags = clean(combined)
            unsigned = parity_step(unsigned, positive)
    for q, polys in all_norms.items():
        assert p_add(*polys) == p_scale(trace_rhs[q], 2)
        COUNTS["exact_dilation_trace_polynomial_equalities"] += 1


def magnitude_moment(exponent, law):
    if law == "finite_magnitudes_1_2_equal_probability":
        return F(1 + 2 ** exponent, 2)
    assert law == "standard_gaussian" and exponent % 2 == 0
    answer = 1
    for j in range(1, exponent, 2):
        answer *= j
    return F(answer)


def expected(poly, law, signed):
    answer = F(0)
    for nu, coefficient in poly.items():
        if signed and any(n % 2 for n in nu):
            continue
        term = coefficient
        for n in nu:
            term *= magnitude_moment(n, law)
        answer += term
    return answer


def conditional_norm_square_fourier(polys):
    # Fourier convolution of the actual scalar squared Euclidean norm.
    fourier = defaultdict(dict)
    for p in polys:
        groups = defaultdict(dict)
        for nu, coefficient in p.items():
            groups[parity(nu)][nu] = coefficient
        for s, a in groups.items():
            for t, b in groups.items():
                fourier[s ^ t] = p_add(fourier[s ^ t], p_mul(a, b))
    return dict(fourier)


def cone_fixtures():
    # Three independent original variables; each entry is an ordinary positive
    # monomial coefficient, including repeated uses of original entries.
    return [
        [{(0, 0, 0): F(1)}, {(0, 0, 0): F(2, 3)}],
        [{(1, 0, 0): F(1), (0, 1, 0): F(2)}, {(0, 0, 1): F(3, 2)}],
        [{(0, 0, 0): F(1), (2, 0, 0): F(1), (1, 1, 0): F(2, 3)},
         {(0, 2, 0): F(1), (0, 0, 2): F(1, 2)}],
        [{(0, 0, 0): F(1), (2, 0, 0): F(1), (1, 1, 0): F(2, 3), (0, 2, 1): F(1)},
         {(1, 0, 0): F(1), (0, 1, 0): F(1), (1, 2, 0): F(1, 2), (0, 0, 3): F(1)}],
        [{(4, 0, 0): F(1), (2, 2, 0): F(2), (1, 1, 2): F(1, 2)},
         {(0, 4, 0): F(1), (0, 0, 0): F(1), (2, 0, 2): F(3, 2)}],
    ]


def check_cone_moments():
    summaries = []
    for polys in cone_fixtures():
        degree = max(sum(nu) for p in polys for nu in p)
        ordinary_square = p_add(*(p_mul(p, p) for p in polys))
        ordinary_fourth = p_mul(ordinary_square, ordinary_square)
        fourier = conditional_norm_square_fourier(polys)
        g = fourier[0]
        conditional_fourth = p_add(*(p_mul(p, p) for p in fourier.values()))
        # Sign averaging deletes the odd-exponent monomials, with no magnitude
        # integration or regularity estimate involved in this exact identity.
        even_ordinary = {nu: a for nu, a in ordinary_fourth.items() if parity(nu) == 0}
        assert conditional_fourth == even_ordinary
        assert g == {nu: a for nu, a in ordinary_square.items() if parity(nu) == 0}
        assert all(a >= 0 for a in g.values())
        COUNTS["conditional_sign_polynomial_identities"] += 2
        for law in ("finite_magnitudes_1_2_equal_probability", "standard_gaussian"):
            norm2 = expected(ordinary_square, law, signed=True)
            norm4 = expected(ordinary_fourth, law, signed=True)
            assert norm2 == expected(g, law, signed=False)
            assert norm4 == expected(conditional_fourth, law, signed=False)
            eg2 = expected(p_mul(g, g), law, signed=False)
            assert norm4 <= 3 ** (2 * degree) * eg2
            # Safe alpha=2 is used only for these two stated calibration laws.
            assert eg2 <= 2 ** (8 * degree) * norm2 ** 2
            assert norm4 <= 3 ** (2 * degree) * 2 ** (8 * degree) * norm2 ** 2
            COUNTS["exact_moment_and_cone_fourth_power_checks"] += 5
            summaries.append({"degree": degree, "law": law,
                              "E_norm_squared": str(norm2), "E_norm_fourth": str(norm4),
                              "E_conditional_second_squared": str(eg2)})
    # Removing a degree-two spectator would change the true norm by its fourth
    # magnitude moment.  This detects amplitude deletion, not only flag errors.
    for law in ("finite_magnitudes_1_2_equal_probability", "standard_gaussian"):
        retained = expected({(4, 0, 4): F(1)}, law, signed=True)
        erased = expected({(4, 0, 0): F(1)}, law, signed=True)
        assert retained == erased * magnitude_moment(4, law) and retained > erased
        COUNTS["even_spectator_moment_non_erasure_checks"] += 1
    return summaries


def main():
    signed = (F(1), F(-2, 3), F(3, 2), F(-5, 4), F(4, 3),
              F(7, 5), F(2, 5), F(-3, 4), F(5, 3))
    cases = (("unit_positive", (F(1),) * M),
             ("unequal_positive_rational", tuple(abs(w) for w in signed)),
             ("unequal_signed_rational", signed))
    for _, weights in cases:
        check_count_blocks(weights)
        check_even_spectators(weights)
        check_vacuum(weights)
    moments = check_cone_moments()
    proof = HERE / "regular_law_positive_cone.md"
    source = Path(__file__).resolve()
    report = {
        "status": "PASS",
        "arithmetic": "exact integers and fractions.Fraction; no floating point",
        "counts": dict(sorted(COUNTS.items())),
        "support": {"shape": [N, N], "original_ordered_edges": EDGES,
                    "weight_cases": [{"name": name, "weights": list(map(str, weights))}
                                     for name, weights in cases]},
        "scope": [
            "Every original monomial of total degree at most 3 at each current vertex; next step degree at most 4.",
            "Creation and annihilation, both current directions: exact orthogonal label partitions and selected-original-submatrix factor followed by parity/count projection.",
            "All nine original exponent slots retained, including an explicit even magnitude spectator outside the selected axis.",
            "Six vacuum roots, lengths 0 through 4, three deterministic weight families; exact ordinary polynomial comparison and original-sign gauge.",
            "Dilation trace polynomial identity for powers 1 through 4, three weight families.",
            "Five explicitly supplied three-variable positive Euclidean polynomial fixtures, degrees 0 through 4; conditional sign identities and exact second/fourth moments for two stated laws.",
        ],
        "limitations": [
            "Finite checks do not establish universal cone hypercontractivity, regular-law strong/weak moments, any asymptotic endpoint, or final same-index deletion.",
            "Signed deterministic weights test geometry and a sign gauge, not coefficient positivity in the bare signed-weight variables. Positivity is asserted for original matrix-entry monomials or after absorbing deterministic signs into independent original signs.",
            "No magnitude is refreshed on reuse. Gaussian tests use exact even moments only and do not enumerate a joint Gaussian law.",
        ],
        "moment_calibrations": moments,
        "pins": {source.name: sha256(source.read_bytes()).hexdigest(),
                 proof.name: sha256(proof.read_bytes()).hexdigest()},
    }
    target = HERE / "regular_law_parity_checks.json"
    target.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "PASS", "counts": report["counts"],
                      "report": str(target), "pins": report["pins"]}, indent=2))


if __name__ == "__main__":
    main()
