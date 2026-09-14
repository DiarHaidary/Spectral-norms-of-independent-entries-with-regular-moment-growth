"""Bounded rational checks for the original-edge repeated-square budget.

No original sign law, exponential-dimensional matrix, or unproved weak
moment supremum is enumerated. Universal statements are analytical.
"""
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from math import factorial
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
COUNTS = Counter()


def check(name, condition):
    COUNTS[name] += 1
    if not condition:
        raise AssertionError(name)


def transpose(matrix):
    return list(map(list, zip(*matrix)))


def multiply(A, B):
    return [[sum(x*y for x, y in zip(row, column))
             for column in zip(*B)] for row in A]


def psd(matrix):
    check('symmetric_positive_certificate_input', matrix == transpose(matrix))
    current = [row[:] for row in matrix]
    for k in range(len(current)):
        pivot = current[k][k]
        check('schur_pivot_nonnegative', pivot >= 0)
        if not pivot:
            check('zero_pivot_has_zero_remaining_row',
                  all(current[k][i] == 0 for i in range(k+1, len(current))))
            continue
        for i in range(k+1, len(current)):
            for j in range(k+1, len(current)):
                current[i][j] -= current[i][k]*current[k][j]/pivot
    COUNTS['exact_positive_matrices'] += 1


def gaussian_moment(half_order):
    value = 1
    for k in range(1, half_order+1):
        value *= 2*k-1
    return F(value)


def entry_moments(rows, columns, gaussian=False, horizon=24):
    result = []
    for edge in range(rows*columns):
        scale = F(edge+2, edge+3)
        if gaussian:
            result.append([scale**(2*h)*gaussian_moment(h)
                           for h in range(horizon+1)])
        else:
            # Independent symmetric laws with total probability 3/4 at |Y|=s
            # and 1/4 at |Y|=2s. These are moment tables indexed by half-order.
            result.append([scale**(2*h)*(F(3, 4)+F(1, 4)*2**(2*h))
                           for h in range(horizon+1)])
    return result


def mass(moments, counts):
    answer = F(1)
    for table, order in zip(moments, counts):
        answer *= table[order]
    return answer


def increment_ratio(moments, counts, increment):
    return mass(moments, [x+y for x, y in zip(counts, increment)]) / mass(moments, counts)


def rectangle_increment(rows, columns, row_pair, column_pair):
    result = [0]*(rows*columns)
    for i, j in product(row_pair, column_pair):
        result[i*columns+j] = 1
    return result


def square_words(rows, columns):
    """Actual eight-step alternating closed words, filtered by edge support.

    Returned list retains each chronological word separately, with its root.
    """
    result = []
    for r in product(range(rows), repeat=4):
        for c in product(range(columns), repeat=4):
            mult = Counter()
            for k in range(4):
                mult[r[k], c[k]] += 1
                mult[r[(k+1) % 4], c[k]] += 1
            if len(mult) != 4 or any(x != 2 for x in mult.values()):
                continue
            used_rows = tuple(sorted({i for i, j in mult}))
            used_columns = tuple(sorted({j for i, j in mult}))
            if len(used_rows) != 2 or len(used_columns) != 2:
                continue
            check('word_support_is_actual_rectangle', set(mult) == set(product(used_rows, used_columns)))
            increment = [0]*(rows*columns)
            for i, j in mult:
                increment[i*columns+j] = 1
            result.append((r[0], used_rows, used_columns, increment))
    for rp in combinations(range(rows), 2):
        for cp in combinations(range(columns), 2):
            for root in rp:
                check('ten_actual_rooted_square_words',
                      sum(v == root and rr == rp and cc == cp for v, rr, cc, _ in result) == 10)
    return result


def conditional_cycle_cases():
    records = []
    for rows, columns in [(2, 2), (3, 2), (3, 3)]:
        words = square_words(rows, columns)
        backgrounds = [[0]*(rows*columns), [edge % 3 for edge in range(rows*columns)],
                       [1 if edge < columns else 0 for edge in range(rows*columns)]]
        for gaussian in [False, True]:
            tables = entry_moments(rows, columns, gaussian)
            for counts in backgrounds:
                V = [[tables[i*columns+j][counts[i*columns+j]+1] /
                      tables[i*columns+j][counts[i*columns+j]]
                      for j in range(columns)] for i in range(rows)]
                row_max = max(map(sum, V))
                column_max = max(map(sum, transpose(V)))
                G = multiply(V, transpose(V))
                G2 = multiply(G, G)
                psd([[row_max*column_max*G[i][j]-G2[i][j]
                      for j in range(rows)] for i in range(rows)])
                root_records = []
                for root in range(rows):
                    by_words = sum(increment_ratio(tables, counts, increment)
                                   for v, _, _, increment in words if v == root)
                    by_rectangles = F(0)
                    for other in range(rows):
                        if root == other:
                            continue
                        for j, l in combinations(range(columns), 2):
                            by_rectangles += 10*V[root][j]*V[root][l]*V[other][j]*V[other][l]
                    identity = 5*sum(G[root][other]**2 -
                                     sum(V[root][j]**2*V[other][j]**2 for j in range(columns))
                                     for other in range(rows) if root != other)
                    check('actual_word_expectation_equals_rooted_contraction', by_words == by_rectangles)
                    check('exact_gram_subtraction_identity', identity == by_rectangles)
                    check('first_cycle_gram_bound', by_rectangles <= 5*G2[root][root])
                    allowance = 5*row_max*column_max*sum(x*x for x in V[root])
                    check('row_column_cycle_variance_bound', by_rectangles <= allowance)
                    if columns == 2:
                        c = [row[0]*row[1] for row in V]
                        check('original_two_edge_rung_factorization', by_rectangles == 10*c[root]*(sum(c)-c[root]))
                    root_records.append({'root': root, 'exact_cycle_cost': str(by_words),
                                         'row_column_allowance': str(allowance)})
                records.append({'rows': rows, 'columns': columns,
                                'law': 'scaled Gaussian' if gaussian else 'scaled symmetric four-point',
                                'background_counts': counts, 'rooted_words': len(words),
                                'roots': root_records})
    return records


def overlap_and_reset_controls():
    tables = entry_moments(3, 2)
    one = rectangle_increment(3, 2, [0, 1], [0, 1])
    two = rectangle_increment(3, 2, [0, 2], [0, 1])
    for counts in [[0]*6, [1, 2, 0, 1, 3, 0]]:
        plus_one = [x+y for x, y in zip(counts, one)]
        plus_two = [x+y for x, y in zip(counts, two)]
        check('overlapping_increment_cocycle',
              increment_ratio(tables, counts, one)*increment_ratio(tables, plus_one, two)
              == increment_ratio(tables, counts, two)*increment_ratio(tables, plus_two, one))
    unit_gaussians = [[gaussian_moment(h) for h in range(20)] for _ in range(6)]
    zero = [0]*6
    shared = increment_ratio(unit_gaussians, one, two)
    repeated = increment_ratio(unit_gaussians, one, one)
    check('shared_rung_fresh_budget_failure_factor_nine', shared == 9)
    check('same_square_fresh_budget_failure_factor_eighty_one', repeated == 81)
    backtrack = [1, 0, 0, 0, 0, 0]
    check('length_ten_occupied_edge_failure_factor_three',
          increment_ratio(unit_gaussians, one, backtrack) == 3)
    repetitions = []
    for ell in range(1, 9):
        counts = [ell*x for x in one]
        value = mass(unit_gaussians, counts)
        check('same_square_all_repetitions_exact', value == gaussian_moment(ell)**4)
        repetitions.append({'number_of_excursions': ell, 'single_word_moment': str(value)})
    return {'distinct_squares_shared_rung_second_cost': str(shared),
            'same_square_second_cost': str(repeated),
            'with_two_ten_word_factors': ['900', '8100'],
            'fresh_rule_with_two_ten_word_factors': '100', 'repetitions': repetitions}


def independent_sum_moment(tables, q):
    """Multinomial moment via truncated exponential-generating convolution."""
    polynomial = [F(1)]+[F(0)]*q
    for table in tables:
        updated = [F(0)]*(q+1)
        for before in range(q+1):
            for add in range(q+1-before):
                updated[before+add] += polynomial[before]*table[add]/factorial(add)
        polynomial = updated
    return polynomial[q]*factorial(q)


def star_and_concatenation_checks():
    records = []
    for degree in [1, 2, 3, 5]:
        for q in range(1, 9):
            table = [gaussian_moment(h) for h in range(q+1)]
            exact = independent_sum_moment([table]*degree, q)
            product_value = 1
            for h in range(q):
                product_value *= degree+2*h
            check('unit_gaussian_star_exact_chi_square_moment', exact == product_value)
    variances = [F(1, 4), F(1), F(9, 4)]
    for q in range(1, 9):
        tables = [[v**h*gaussian_moment(h) for h in range(q+1)] for v in variances]
        exact = independent_sum_moment(tables, q)
        upper = F(1)
        for h in range(q):
            upper *= sum(variances)+2*h*max(variances)
        check('weighted_gaussian_star_variance_budget', exact <= upper)
        records.append({'family': 'weighted Gaussian star', 'q': q,
                        'exact_moment': str(exact), 'variance_budget': str(upper)})
    for partners in [1, 2, 4]:
        for ell in range(1, 8):
            table = [gaussian_moment(h)**2 for h in range(ell+1)]
            exact_sum = independent_sum_moment([table]*partners, ell)
            upper_sum = F(1)
            for h in range(ell):
                upper_sum *= partners+4*h*(h+1)
            check('gaussian_rung_sum_allocation_budget', exact_sum <= upper_sum)
            exact_excursions = F(10)**ell*table[ell]*exact_sum
            upper_excursions = F(10)**ell*table[ell]*upper_sum
            check('concatenated_rooted_cycle_family_bound', exact_excursions <= upper_excursions)
            records.append({'family': 'concatenated Gaussian square excursions',
                            'partner_rungs': partners, 'excursions': ell, 'word_length': 8*ell,
                            'exact_moment': str(exact_excursions), 'allowance': str(upper_excursions)})
    return records


def main():
    report = {'status': 'PASS', 'arithmetic': 'exact rational arithmetic and Schur positivity',
              'conditional_cycle_cases': conditional_cycle_cases(),
              'reset_counterexamples': overlap_and_reset_controls(),
              'star_and_concatenation_cases': star_and_concatenation_checks()}
    report['counts'] = dict(sorted(COUNTS.items()))
    report['total_checks'] = sum(COUNTS.values())
    report['scope'] = ['actual length-eight alternating words on K_(2,2), K_(3,2), K_(3,3)',
                       'selected even-multiplicity backgrounds and original-entry moment laws',
                       'no sign-law enumeration or general weak-moment optimization',
                       'no coverage assertion for arbitrary interleaved cycle words',
                       'no full MI-32, amplitude-transfer, or quantile conclusion']
    report['files'] = {name: sha256((HERE/name).read_bytes()).hexdigest() for name in
                       ['verify_cycle_multiplicity.py', 'cycle_multiplicity.md']}
    target = HERE/'cycle_multiplicity_checks.json'
    target.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'status': report['status'], 'total_checks': report['total_checks'],
                      'report': str(target)}))


if __name__ == '__main__':
    main()
