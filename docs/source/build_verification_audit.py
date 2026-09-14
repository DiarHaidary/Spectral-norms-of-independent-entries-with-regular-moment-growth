"""Record reviewed mathematics, bounded evidence, and checkpoint integrity.

This does not formally prove any theorem and does not rerun mathematical suites.
It checks all reported file hashes and preserves the exact declared scopes.
"""
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import json
import re

HERE = Path(__file__).resolve().parent
CONTINUED = HERE.parent


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def pin(path, label=None):
    return {'path': label or str(path), 'sha256': digest(path),
            'bytes': path.stat().st_size}


def prior_integrity(path):
    data = json.loads(path.read_text(encoding='utf-8-sig'))
    counts = {}
    for key in ('artifacts', 'source_pins'):
        count = 0
        for record in data.get(key, []):
            if not record.get('path') or not record.get('sha256'):
                continue
            target = Path(record['path'])
            if not target.is_absolute():
                target = path.parent / target
            assert target.is_file(), str(target)
            assert digest(target) == record['sha256'].lower(), str(target)
            count += 1
        counts[key] = count
    return {**pin(path), 'status': 'PASS', 'matching_pins': counts,
            'scope': 'All recorded artifact and source pins checked; old mathematical suites not rerun.'}


def resolve_report_path(name):
    target = Path(name)
    if target.is_absolute():
        assert target.is_file(), str(target)
        return target.resolve()
    choices = [p.resolve() for p in (HERE / target, CONTINUED / target) if p.is_file()]
    assert len(set(choices)) == 1, (name, choices)
    return choices[0]


def report_pins(data, proof, script):
    records = []
    for key in ('dependencies', 'files', 'sha256', 'pins'):
        value = data.get(key, {})
        if isinstance(value, dict):
            records += [{'path': name, 'sha256': value_} for name, value_ in value.items()]
        else:
            records += value
    if 'proof_sha256' in data:
        records.append({'path': proof, 'sha256': data['proof_sha256']})
    if 'verifier_sha256' in data:
        records.append({'path': script, 'sha256': data['verifier_sha256']})
    if 'archived_negative_control_source' in data:
        records.append({'path': data['archived_negative_control_source'],
                        'sha256': data['archived_negative_control_sha256']})
    checked = set()
    for record in records:
        target = resolve_report_path(record['path'])
        assert digest(target) == record['sha256'].lower(), str(target)
        checked.add(target)
    assert (HERE / proof).resolve() in checked, proof
    assert (HERE / script).resolve() in checked, script
    return checked


def links_in(artifacts):
    links, external = [], set()
    for path in artifacts:
        if path.suffix != '.md':
            continue
        lines, fenced, display = [], False, False
        for line in path.read_text(encoding='utf-8-sig').splitlines():
            if line.lstrip().startswith('```'):
                fenced = not fenced
                continue
            if line.strip() == r'\[':
                display = True
                continue
            if line.strip() == r'\]':
                display = False
                continue
            if not fenced and not display and not line.startswith(('    ', '\t')):
                lines.append(re.sub(r'`[^`]*`', '', line))
        for match in re.finditer(r'\[[^\]]*\]\((<[^>]+>|[^)]+)\)', '\n'.join(lines)):
            target = match.group(1).strip('<>').split('#')[0]
            if not target or target.startswith(('https://', 'http://', 'mailto:')):
                continue
            destination = (path.parent / target).resolve()
            assert destination == HERE / 'verification_audit.json' or destination.is_file(), (path.name, target)
            links.append({'file': path.name, 'target': target})
            if destination.parent != HERE:
                external.add(destination)
    return links, external


def main():
    groups = [
        ('cycle_fiber_geometry.md', 'verify_cycle_fiber_geometry.py', 'cycle_fiber_geometry_checks.json'),
        ('cycle_transfer.md', 'verify_cycle_transfer.py', 'cycle_transfer_checks.json'),
        ('ordered_cycle_boundary.md', 'verify_ordered_cycle.py', 'ordered_cycle_checks.json'),
        ('cycle_multiplicity.md', 'verify_cycle_multiplicity.py', 'cycle_multiplicity_checks.json'),
        ('regular_law_positive_cone.md', 'verify_positive_cone.py', 'positive_cone_checks.json'),
        ('regular_law_positive_cone.md', 'verify_regular_law_parity.py', 'regular_law_parity_checks.json'),
    ]
    required = {'README.md', 'MI32_solution.md', 'progress.md', 'build_verification_audit.py',
                'weighted_sign_localization.md', 'weighted_sign_deletion.md',
                'regular_law_deletion.md', 'full_law_conditioning_frontier.md'}
    required.update(name for group in groups for name in group)
    artifacts = sorted((HERE / name for name in required), key=lambda p: p.name)
    assert all(path.is_file() for path in artifacts)
    # All deliverable Markdown, Python and JSON files must be accounted for.
    found = {p.name for p in HERE.iterdir() if p.is_file() and p.suffix in ('.md', '.py', '.json')}
    assert found - {'verification_audit.json'} == required, sorted(found.symmetric_difference(required))
    old_paths = [CONTINUED / 'verification_audit_2026-09-13.json']
    old_paths += [CONTINUED / folder / 'verification_audit.json' for folder in [
        'reused_boundary_2026-09-13', 'collective_rows_2026-09-13', 'projected_boundary_2026-09-13',
        'interleaved_boundary_2026-09-13', 'occupation_interference_2026-09-13',
        'residual_word_2026-09-13', 'mi32_frontier_2026-09-13',
        'mi32_exchange_2026-09-13', 'mi32_profile_2026-09-13']]
    previous = [prior_integrity(path) for path in old_paths]
    sources = set(old_paths)
    sources.update(Path(r'C:\Users\Diar\Desktop\Proofs') / name for name in [
        'SparseStack.tex', 'SRHT.tex', 'Proof_Method_standalone.tex', 'Sharp Bounds for Graph Matrices.tex'])
    reports = {}
    for proof, script, report_name in groups:
        data = json.loads((HERE / report_name).read_text(encoding='utf-8-sig'))
        assert data['status'].upper() in ('PASS', 'PASSED'), report_name
        checked = report_pins(data, proof, script)
        sources.update(p for p in checked if p.parent != HERE)
        reports[report_name] = data
    geometry = reports['cycle_fiber_geometry_checks.json']
    assert geometry['counts']['exact_global_gram_equalities'] == 16
    assert geometry['arbitrary_count_blocks']['counts']['exact_selected_submatrix_factor_rows'] == 2062
    assert reports['cycle_transfer_checks.json']['counts'] == {
        'exact_equalities': 28, 'exact_psd_checks': 15, 'nonzero_or_failure_controls': 1}
    assert reports['ordered_cycle_checks.json']['matrix_checks'] == {
        'matrix_equalities': 118, 'exact_psd_checks': 42, 'nonzero_controls': 3}
    assert reports['cycle_multiplicity_checks.json']['total_checks'] == 693
    cone = reports['positive_cone_checks.json']
    assert cone['total_exact_assertions'] == 6349 and cone['positive_case_count'] == 23
    assert cone['amplitude_states_per_case'] == 12 and cone['original_signed_states_per_case'] == 160
    parity = reports['regular_law_parity_checks.json']
    assert parity['counts']['exact_submatrix_compression_equalities'] == 324
    assert parity['counts']['individual_transition_count_invariants'] == 11880
    assert parity['counts']['exact_dilation_trace_polynomial_equalities'] == 12
    links, external = links_in(artifacts)
    sources.update(external)
    result = {
        'created_utc': datetime.now(timezone.utc).isoformat(),
        'status': 'PASS within recorded analytic-review, exact finite evidence, and integrity scopes',
        'proof_status': {
            'full_MI32_upper': 'Proved in regular_law_positive_cone.md and regular_law_deletion.md; independently reviewed.',
            'full_MI32_lower': 'Established primary result: Latala--Swiatkowski Theorem 4.1, not a new lower proof.',
            'goal_objective': 'Solve MI-32 and advance our methodology in parallel, stop when you have solved MI-32.',
            'goal_completion': 'The proof and checkpoint satisfy the objective; goal-tool completion follows this successful final audit.',
            'three_original_proof_calculus': 'Advanced by a shared graph/Parseval/SRHT inclusion bridge; not claimed complete in full generality.',
            'formal_proof_assistant_certification': False,
            'matching_quantiles_claimed': False,
        },
        'artifacts': [pin(path, path.name) for path in artifacts],
        'source_pins': [pin(path) for path in sorted(sources, key=str)],
        'previous_checkpoint_integrity': previous,
        'local_markdown_links': links,
        'analytic_reviews': [
            {'files': ['weighted_sign_localization.md'], 'reviewers': ['/root/variance_profile', '/root/profile_transfer', '/root/moment_ratio'], 'status': 'PASS', 'scope': 'Exact count blocks, actual submatrix compression, primary strong/weak moments, small-axis net, Hilbert Boolean HC, constants and vacuum trace; added vertex-variance congruence independently checked by root, variance_profile and moment_ratio.'},
            {'files': ['regular_law_positive_cone.md'], 'reviewers': ['/root/variance_profile', '/root/profile_transfer', '/root/moment_ratio'], 'status': 'PASS', 'scope': 'Moment submultiplication, positive coefficient cone, interpolation, parity-compatible magnitude spectators, separate creator and annihilator decompositions, full-regular SW assumptions, all horizon/dimension costs and actual vacuum iteration.'},
            {'files': ['weighted_sign_deletion.md'], 'reviewers': ['/root'], 'status': 'PASS', 'scope': 'Published implication applicability, original symmetric signs, scalar order doubling down to log2, paired deletion and known lower attribution.'},
            {'files': ['regular_law_deletion.md'], 'reviewers': ['/root', '/root/moment_ratio'], 'status': 'PASS', 'scope': 'Full primary Remark4.5 interface; random diagonal, nonprincipal and masked symmetric blocks, small-exponent moments, paired dilation, nonsymmetric symmetrization and exact original D.'},
            {'files': ['cycle_fiber_geometry.md', 'cycle_transfer.md', 'cycle_multiplicity.md'], 'reviewers': ['/root'], 'status': 'PASS', 'scope': 'Full cycle, original-label, supplied coefficient, exact continuation and original multiplicity claims, with structural limits retained.'},
            {'files': ['ordered_cycle_boundary.md'], 'reviewers': ['/root/moment_ratio'], 'status': 'PASS', 'scope': 'Ordered nilpotent boundary, actual tensor/grade restrictions, positive budgets, sequential identification and standard-source attribution.'},
            {'files': ['full_law_conditioning_frontier.md'], 'reviewers': ['/root'], 'status': 'PASS', 'scope': 'Fixed-subset SW/net estimate, Gaussian-diagonal selection counterexample and explicitly charged alternative selection loss.'},
            {'files': ['MI32_solution.md', 'README.md', 'progress.md'], 'reviewers': ['/root/profile_transfer', '/root/moment_ratio'], 'status': 'PASS', 'scope': 'Proof map, original motivation, new upper versus established lower, input classes, useful regimes, and separation from quantiles and a complete three-model calculus.'},
        ],
        'implementation_reviews': [
            {'files': ['build_verification_audit.py'], 'reviewers': ['/root/profile_transfer'], 'status': 'PASS', 'scope': 'Read-only review of all report-pin schemas, exact scopes and review chronology, six report groups, ten preceding checkpoints, source resolution and integration metadata. Corrections applied for parity pins and retention of separate report limitations.'},
            {'files': ['verify_cycle_fiber_geometry.py', 'cycle_fiber_geometry_checks.json'], 'reviewers': ['/root', '/root/profile_transfer'], 'status': 'PASS', 'scope': 'Both reviewed the original rung and arbitrary-count checks through Section9. Root separately reviewed the later Section10 Parseval insertion and its exact difference-square checks.'},
            {'files': ['verify_cycle_transfer.py', 'cycle_transfer_checks.json'], 'reviewers': ['/root/variance_profile'], 'status': 'PASS'},
            {'files': ['verify_ordered_cycle.py', 'ordered_cycle_checks.json'], 'reviewers': ['/root/moment_ratio'], 'status': 'PASS'},
            {'files': ['verify_cycle_multiplicity.py', 'cycle_multiplicity_checks.json'], 'reviewers': ['/root'], 'status': 'PASS'},
            {'files': ['verify_positive_cone.py', 'positive_cone_checks.json'], 'reviewers': ['/root'], 'status': 'PASS'},
            {'files': ['verify_regular_law_parity.py', 'regular_law_parity_checks.json'], 'reviewers': ['/root'], 'status': 'PASS'},
        ],
        'executable_evidence': [{'report': name, 'status': data['status'],
            'counts': data.get('counts', data.get('matrix_checks', {})),
            'scope': data.get('scope', data.get('limits', [])),
            'limitations': data.get('limitations', data.get('limits', []))} for name, data in reports.items()],
        'primary_sources_consulted': [
            'https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/matrix-inequalities-and-norms/MI-32/README.md',
            'https://arxiv.org/html/2106.03139v2',
            'https://arxiv.org/pdf/1612.02407',
            'https://arxiv.org/pdf/math/9206201',
            'https://www.cs.cmu.edu/~odonnell/boolean-analysis/lecture16.pdf',
            'https://arxiv.org/html/2405.13656v2',
            'https://arxiv.org/html/2512.23673v2',
            'https://access.archive-ouverte.unige.ch/access/metadata/2e3d55fc-f7d2-42af-95ae-6c06df864dbb/download',
        ],
        'limitations': [
            'Finite checks support exact identities and counterexamples; they do not certify universal theorems.',
            'Analytic proof reviews are independent agent reviews, not journal peer review or proof-assistant certification.',
            'The general-law contraction is on positive original-monomial polynomials, not arbitrary signed polynomials or a raw Jacobi span.',
            'No matching-quantile theorem or efficient evaluation algorithm for D or weak moments is asserted.',
            'The original three-model analytic calculus is advanced but not declared finished for arbitrary further interactions.',
            'No external publication, messages to others, or shutdown performed.',
        ],
        'immutable_scope': 'All listed deliverables and sources pinned. This audit and mutable ../LATEST.md self-excluded.',
    }
    (HERE / 'verification_audit.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'status': 'PASS', 'artifacts': len(artifacts), 'source_pins': len(sources),
                      'previous_checkpoints': len(previous), 'mathematical_suites': len(groups),
                      'local_links': len(links)}, indent=2))


if __name__ == '__main__':
    main()
