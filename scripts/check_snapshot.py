#!/usr/bin/env python3
"""Validate the checked source snapshot and, optionally, a fresh Lean axiom audit."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--axioms-log', type=Path, help='Output of lake env lean AxiomAudit.lean')
args = parser.parse_args()
snapshot = json.loads((ROOT / 'verification/snapshot.json').read_text())
expected = {row['source']: row for row in snapshot['source_checks']}
actual = {str(p.relative_to(ROOT)) for p in (ROOT / 'SpectralRadiusUpperTail').glob('*.lean')}
actual.update({'SpectralRadiusUpperTail.lean', 'AxiomAudit.lean'})
if set(expected) != actual:
    sys.exit(f'Source inventory differs from the snapshot: {set(expected) ^ actual}')
for name, row in expected.items():
    contents = (ROOT / name).read_bytes()
    if hashlib.sha256(contents).hexdigest() != row['sha256']:
        sys.exit(f'Source hash differs from the checked snapshot: {name}')
    if not row['passed']:
        sys.exit(f'Snapshot has a failed source check: {name}')
    text = contents.decode('utf-8')
    if re.search(r'\bsorry\b|^\s*axiom\s|set_option\s+(maxHeartbeats|maxRecDepth)', text, re.M):
        sys.exit(f'Placeholder, axiom declaration, or checking-limit override: {name}')
imports = re.findall(r'^import SpectralRadiusUpperTail\.(\w+)$',
                     (ROOT / 'SpectralRadiusUpperTail.lean').read_text(), re.M)
modules = {Path(name).stem for name in actual if name.startswith('SpectralRadiusUpperTail/')}
if len(imports) != len(set(imports)) or set(imports) != modules:
    sys.exit('Aggregate imports do not cover each project module exactly once.')
seen = set()
for name in imports:
    dependencies = re.findall(r'^import SpectralRadiusUpperTail\.(\w+)$',
                             (ROOT / 'SpectralRadiusUpperTail' / f'{name}.lean').read_text(), re.M)
    if not set(dependencies) <= seen:
        sys.exit(f'Aggregate imports are not in dependency order at {name}.')
    seen.add(name)
audit = (ROOT / 'AxiomAudit.lean').read_text()
names = re.findall(r'^#print axioms (\S+)$', audit, re.M)
if len(names) != len(set(names)) or len(names) != snapshot['named_declarations_audited']:
    sys.exit('Axiom-audit declaration inventory differs from the snapshot.')
if args.axioms_log:
    log = args.axioms_log.read_text()
    if re.search(r'\bsorryAx\b|declaration uses `sorry`|\berror(?:\(|:)', log):
        sys.exit('Lean reported a proof error or incomplete proof in the audit log.')
    allowed = {'propext', 'Classical.choice', 'choice', 'Quot.sound', ''}
    reported = set(re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)", log))
    if not set(names) <= reported:
        sys.exit(f'Audit log is incomplete: {len(set(names) - reported)} declarations missing.')
    for block in re.findall(r'depends on axioms:\s*\[([^]]*)\]', log):
        unexpected = set(re.sub(r'\s+', '', block).split(',')) - allowed
        if unexpected:
            sys.exit(f'Unexpected axioms: {unexpected}')
    print(f'Fresh axiom log covers all {len(names)} declarations using only standard axioms.')
print(f'Snapshot matches: {len(modules)} modules, {len(expected)} source hashes, '
      f'{len(names)} audited declarations; dependency order valid.')
