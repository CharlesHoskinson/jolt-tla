#!/usr/bin/env python3
"""
check_alignment.py - Verify constants alignment across TLA+ and manifest

This script extracts constants from:
- docs/constants.json (canonical manifest)
- tla/Registry.tla (RequiredKeys, ExternalHandleTags)
- tla/Hash.tla (ALL_DOMAIN_TAGS)
- tla/Transcript.tla (TYPE_*_FR)

Exit code 0 = all aligned, non-zero = drift detected
"""

import json
import re
import sys
from pathlib import Path

# ANSI colors for output
RED = "\033[91m"
GREEN = "\033[92m"
YELLOW = "\033[93m"
RESET = "\033[0m"


def load_manifest(path: Path) -> dict:
    """Load the canonical constants manifest."""
    with open(path) as f:
        return json.load(f)


def extract_string_constants(content: str, prefix: str) -> dict:
    """Extract string constant definitions like 'PREFIX_NAME == "value"'."""
    pattern = rf'({prefix}[\w_]+)\s*==\s*"([^"]+)"'
    return dict(re.findall(pattern, content))


def extract_numeric_constants(content: str, prefix: str) -> dict:
    """Extract numeric constant definitions like 'PREFIX_NAME == 123'."""
    pattern = rf'({prefix}[\w_]+)\s*==\s*(\d+)'
    matches = re.findall(pattern, content)
    return {name: int(value) for name, value in matches}


def extract_tla_set_refs(content: str, set_name: str) -> list:
    """Extract variable references from a TLA+ set definition."""
    # Match set definition spanning multiple lines
    pattern = rf'{set_name}\s*==\s*\{{\s*([^}}]+)\}}'
    match = re.search(pattern, content, re.DOTALL)
    if not match:
        return []

    set_content = match.group(1)
    # Extract variable references (identifiers that aren't keywords)
    refs = re.findall(r'\b([A-Z][A-Z0-9_]+)\b', set_content)
    # Filter out TLA+ keywords and operators
    keywords = {'IF', 'THEN', 'ELSE', 'LET', 'IN', 'TRUE', 'FALSE', 'EXCEPT', 'DOMAIN', 'CHOOSE'}
    return [r for r in refs if r not in keywords]


def resolve_refs(refs: list, definitions: dict) -> set:
    """Resolve variable references to their string values."""
    resolved = set()
    for ref in refs:
        if ref in definitions:
            resolved.add(definitions[ref])
    return resolved


def check_registry_alignment(manifest: dict, registry_content: str) -> list:
    """Check registry keys alignment."""
    errors = []

    # Extract KEY_* and EXTERNAL_* definitions
    key_defs = extract_string_constants(registry_content, "KEY_")
    external_defs = extract_string_constants(registry_content, "EXTERNAL_")

    # Extract RequiredKeys set references and resolve
    required_refs = extract_tla_set_refs(registry_content, "RequiredKeys")
    tla_required = resolve_refs(required_refs, key_defs)
    manifest_required = set(manifest["registry"]["required_keys"])

    if tla_required != manifest_required:
        missing_in_tla = manifest_required - tla_required
        extra_in_tla = tla_required - manifest_required
        if missing_in_tla:
            errors.append(f"Registry: Missing in TLA RequiredKeys: {sorted(missing_in_tla)}")
        if extra_in_tla:
            errors.append(f"Registry: Extra in TLA RequiredKeys: {sorted(extra_in_tla)}")

    # Check count
    tla_count_match = re.search(r'Cardinality\(RequiredKeys\)\s*=\s*(\d+)', registry_content)
    if tla_count_match:
        tla_count = int(tla_count_match.group(1))
        if tla_count != manifest["registry"]["required_keys_count"]:
            errors.append(f"Registry: Count mismatch - TLA={tla_count}, manifest={manifest['registry']['required_keys_count']}")

    # Extract ExternalHandleTags and resolve
    external_refs = extract_tla_set_refs(registry_content, "ExternalHandleTags")
    tla_external = resolve_refs(external_refs, external_defs)
    manifest_external = set(manifest["registry"]["external_handles"])

    if tla_external != manifest_external:
        missing = manifest_external - tla_external
        extra = tla_external - manifest_external
        if missing:
            errors.append(f"Registry: Missing in TLA ExternalHandleTags: {sorted(missing)}")
        if extra:
            errors.append(f"Registry: Extra in TLA ExternalHandleTags: {sorted(extra)}")

    return errors


def check_hash_alignment(manifest: dict, hash_content: str) -> list:
    """Check domain tags alignment."""
    errors = []

    # Extract TAG_* definitions
    tag_defs = extract_string_constants(hash_content, "TAG_")

    # Extract ALL_DOMAIN_TAGS set references and resolve
    tag_refs = extract_tla_set_refs(hash_content, "ALL_DOMAIN_TAGS")
    tla_tags = resolve_refs(tag_refs, tag_defs)
    manifest_tags = set(manifest["domain_tags"]["tags"])

    if tla_tags != manifest_tags:
        missing = manifest_tags - tla_tags
        extra = tla_tags - manifest_tags
        if missing:
            errors.append(f"Hash: Missing in TLA ALL_DOMAIN_TAGS: {sorted(missing)}")
        if extra:
            errors.append(f"Hash: Extra in TLA ALL_DOMAIN_TAGS: {sorted(extra)}")

    # Check count assertion
    count_match = re.search(r'Cardinality\(ALL_DOMAIN_TAGS\)\s*=\s*(\d+)', hash_content)
    if count_match:
        tla_count = int(count_match.group(1))
        if tla_count != manifest["domain_tags"]["tags_count"]:
            errors.append(f"Hash: Count mismatch - TLA={tla_count}, manifest={manifest['domain_tags']['tags_count']}")

    # Check for stale comments (case-insensitive search for "12 domain tags")
    if re.search(r'\b12\s+domain\s+tags\b', hash_content, re.IGNORECASE):
        errors.append("Hash: Stale comment mentions '12 domain tags' but should be 17")

    return errors


def check_transcript_alignment(manifest: dict, transcript_content: str) -> list:
    """Check transcript type tags alignment."""
    errors = []

    # Extract TYPE_*_FR constants
    type_tags = extract_numeric_constants(transcript_content, "TYPE_")
    manifest_tags = manifest["transcript"]["type_tags"]

    for name, expected_value in manifest_tags.items():
        if name not in type_tags:
            errors.append(f"Transcript: Missing {name} in TLA")
        elif type_tags[name] != expected_value:
            errors.append(f"Transcript: {name} mismatch - TLA={type_tags[name]}, manifest={expected_value}")

    # Check for extra type tags in TLA
    for name in type_tags:
        if name.endswith("_FR") and name not in manifest_tags:
            errors.append(f"Transcript: Extra type tag in TLA: {name}")

    return errors


def check_poseidon_alignment(manifest: dict, hash_content: str) -> list:
    """Check Poseidon parameters alignment."""
    errors = []

    poseidon_params = {
        "POSEIDON_WIDTH": manifest["poseidon"]["width"],
        "POSEIDON_RATE": manifest["poseidon"]["rate"],
        "POSEIDON_CAPACITY": manifest["poseidon"]["capacity"],
        "POSEIDON_FULL_ROUNDS": manifest["poseidon"]["full_rounds"],
        "POSEIDON_PARTIAL_ROUNDS": manifest["poseidon"]["partial_rounds"],
        "POSEIDON_SBOX_ALPHA": manifest["poseidon"]["sbox_alpha"],
        "POSEIDON_SECURITY_BITS": manifest["poseidon"]["security_bits"],
    }

    # Extract all POSEIDON_* numeric constants
    poseidon_defs = extract_numeric_constants(hash_content, "POSEIDON_")

    for param, expected in poseidon_params.items():
        if param in poseidon_defs:
            actual = poseidon_defs[param]
            if actual != expected:
                errors.append(f"Poseidon: {param} mismatch - TLA={actual}, manifest={expected}")
        else:
            errors.append(f"Poseidon: {param} not found in Hash.tla")

    # Check total rounds formula (derived, not necessarily defined separately)
    if "POSEIDON_TOTAL_ROUNDS" in poseidon_defs:
        expected_total = manifest["poseidon"]["total_rounds"]
        if poseidon_defs["POSEIDON_TOTAL_ROUNDS"] != expected_total:
            errors.append(f"Poseidon: POSEIDON_TOTAL_ROUNDS mismatch")
    else:
        # Check if it's defined as a formula
        if re.search(r'POSEIDON_TOTAL_ROUNDS\s*==\s*POSEIDON_FULL_ROUNDS\s*\+\s*POSEIDON_PARTIAL_ROUNDS', hash_content):
            # Formula is correct, verify manifest matches
            computed = manifest["poseidon"]["full_rounds"] + manifest["poseidon"]["partial_rounds"]
            if computed != manifest["poseidon"]["total_rounds"]:
                errors.append(f"Poseidon: manifest total_rounds ({manifest['poseidon']['total_rounds']}) != full + partial ({computed})")

    return errors


def main():
    # Determine paths relative to script location
    script_dir = Path(__file__).parent
    repo_root = script_dir.parent

    manifest_path = repo_root / "docs" / "constants.json"
    registry_path = repo_root / "tla" / "Registry.tla"
    hash_path = repo_root / "tla" / "Hash.tla"
    transcript_path = repo_root / "tla" / "Transcript.tla"

    # Check all files exist
    missing = []
    for path in [manifest_path, registry_path, hash_path, transcript_path]:
        if not path.exists():
            missing.append(str(path))

    if missing:
        print(f"{RED}ERROR: Missing files:{RESET}")
        for m in missing:
            print(f"  - {m}")
        sys.exit(2)

    # Load manifest
    print(f"Loading manifest from {manifest_path}")
    manifest = load_manifest(manifest_path)
    print(f"  Version: {manifest.get('version', 'unknown')}")

    # Load TLA files
    registry_content = registry_path.read_text()
    hash_content = hash_path.read_text()
    transcript_content = transcript_path.read_text()

    # Collect all errors
    all_errors = []

    print("\nChecking Registry alignment...")
    errors = check_registry_alignment(manifest, registry_content)
    all_errors.extend(errors)
    if errors:
        for e in errors:
            print(f"  {RED}FAIL:{RESET} {e}")
    else:
        print(f"  {GREEN}PASS:{RESET} Registry keys aligned (17 required, 3 external)")

    print("\nChecking Hash/Domain Tags alignment...")
    errors = check_hash_alignment(manifest, hash_content)
    all_errors.extend(errors)
    if errors:
        for e in errors:
            print(f"  {RED}FAIL:{RESET} {e}")
    else:
        print(f"  {GREEN}PASS:{RESET} Domain tags aligned (17 tags)")

    print("\nChecking Transcript Type Tags alignment...")
    errors = check_transcript_alignment(manifest, transcript_content)
    all_errors.extend(errors)
    if errors:
        for e in errors:
            print(f"  {RED}FAIL:{RESET} {e}")
    else:
        print(f"  {GREEN}PASS:{RESET} Type tags aligned (4 tags)")

    print("\nChecking Poseidon Parameters alignment...")
    errors = check_poseidon_alignment(manifest, hash_content)
    all_errors.extend(errors)
    if errors:
        for e in errors:
            print(f"  {RED}FAIL:{RESET} {e}")
    else:
        print(f"  {GREEN}PASS:{RESET} Poseidon parameters aligned")

    # Summary
    print("\n" + "=" * 50)
    if all_errors:
        print(f"{RED}ALIGNMENT CHECK FAILED{RESET}")
        print(f"Found {len(all_errors)} issue(s)")
        sys.exit(1)
    else:
        print(f"{GREEN}ALIGNMENT CHECK PASSED{RESET}")
        print("All constants aligned between manifest and TLA+")
        sys.exit(0)


if __name__ == "__main__":
    main()
