from collections import Counter
from hashlib import sha256
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# Logical target pins from 9cfb680e22c66013943c36834d483ad1b69e0ecd.
# Comments and whitespace outside string literals are excluded, not mathematical code.
TARGET_CODE_DIGESTS = {
    "EulerNonuniqueness/Definitions.lean": "a968c5549f312652914deb43a1c3d3953947291b0ef53db008960d7b888ea495",
    "EulerNonuniqueness/Statement.lean": "1bbd060a7d785448b6348f22b0b5f5924f5ca0d43935e22ed8c185e5e6066ee0",
    "Challenge.lean": "019605c38123af4f7ce9fcaa1a5ff5b356cd0fa7e9e0abc1f76f8876d3cd6679",
    "Comparator.lean": "59e02c8b7fa5c3d3f68f0f0ad5cbda14b5b7369b3ddce24265a1f58f55fd493c",
}
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|axiom|unsafe|native_decide|sorryAx|implemented_by|extern|"
    r"ofReduceBool|ofReduceNat|trustLevel|skipKernelTC)\b"
)
SMOOTH_TEST_FILES = {
    "Challenge.lean",
    "EulerNonuniqueness/Definitions.lean",
    "EulerNonuniqueness/Section8/CompactnessStatement.lean",
    "EulerNonuniqueness/Section8/Assembly.lean",
}


def lean_code(source, preserve_strings=False):
    result = []
    offset = 0
    depth = 0
    quoted = False
    while offset < len(source):
        current = source[offset]
        pair = source[offset:offset + 2]
        if depth:
            if pair == "/-":
                depth += 1
                result.extend("  ")
                offset += 2
            elif pair == "-/":
                depth -= 1
                result.extend("  ")
                offset += 2
            else:
                result.append("\n" if current == "\n" else " ")
                offset += 1
        elif quoted:
            if current == "\\":
                result.extend(source[offset:offset + 2] if preserve_strings else "  ")
                offset += 2
            else:
                if current == '"':
                    quoted = False
                result.append(current if preserve_strings else ("\n" if current == "\n" else " "))
                offset += 1
        elif pair == "/-":
            depth = 1
            result.extend("  ")
            offset += 2
        elif pair == "--":
            end = source.find("\n", offset)
            if end == -1:
                end = len(source)
            result.extend(" " * (end - offset))
            offset = end
        elif current == '"':
            quoted = True
            result.append('"' if preserve_strings else " ")
            offset += 1
        else:
            result.append(current)
            offset += 1
    if depth or quoted:
        raise ValueError("Unterminated Lean comment or string")
    return "".join(result)


def normalized_logical_digest(source):
    """Pin comment-free code, retaining string contents and normalizing other whitespace."""
    code = lean_code(source, preserve_strings=True)
    tokens = re.findall(r'"(?:\\[\s\S]|[^"\\])*"|[^\s"]+', code)
    return sha256(" ".join(tokens).encode("utf-8")).hexdigest()


def declared_theorems(code):
    blocks = []
    names = []
    for line in code.splitlines():
        command = line.strip()
        command = re.sub(r"^(?:@\[[^\]]*\]\s*)+", "", command)
        namespace = re.fullmatch(r"namespace\s+(\S+)", command)
        section = re.fullmatch(r"(?:noncomputable\s+)?section(?:\s+(\S+))?", command)
        closing = re.fullmatch(r"end(?:\s+(\S+))?", command)
        declaration = re.match(r"(?:theorem|lemma)\s+(\S+)", command)
        if namespace:
            blocks.append((namespace.group(1), True))
        elif section:
            blocks.append((section.group(1), False))
        elif closing:
            if not blocks:
                raise ValueError("Unmatched end")
            if closing.group(1):
                while blocks and blocks[-1][0] != closing.group(1):
                    blocks.pop()
                if not blocks:
                    raise ValueError("Unmatched named end")
            blocks.pop()
        elif declaration:
            names.append(".".join(
                [name for name, is_namespace in blocks if is_namespace]
                + [declaration.group(1)]
            ))
    return names


def check_sources():
    paths = sorted((ROOT / "EulerNonuniqueness").rglob("*.lean"))
    paths += sorted(ROOT.glob("*.lean"))
    names = []
    for path in paths:
        code = lean_code(path.read_text())
        found = FORBIDDEN.search(code)
        if found:
            raise ValueError(f"Forbidden token {found.group()} in {path.relative_to(ROOT)}")
        if path.name == "Challenge.lean":
            imports = re.findall(r"^import\s+(\S+)\s*$", code, re.MULTILINE)
            if imports != ["Mathlib"]:
                raise ValueError("Independent challenge must import only Mathlib")
        if path.relative_to(ROOT).as_posix() in SMOOTH_TEST_FILES:
            if re.search(r"\bContDiff\s+ℝ\s+(?:⊤|ω)(?:\s|$)", code):
                raise ValueError(f"Analytic rather than smooth test class in {path.relative_to(ROOT)}")
        names.extend(declared_theorems(code))
    duplicates = sorted(name for name, count in Counter(names).items() if count > 1)
    if duplicates:
        raise ValueError(f"Duplicate theorem declaration names: {duplicates}")
    audit_code = lean_code((ROOT / "Audit.lean").read_text())
    audited = re.findall(r"^#print axioms\s+(\S+)\s*$", audit_code, re.MULTILINE)
    if Counter(names) != Counter(audited):
        raise ValueError(f"Audit coverage differs: missing={Counter(names) - Counter(audited)}, "
                         f"extra={Counter(audited) - Counter(names)}")
    for relative, expected in TARGET_CODE_DIGESTS.items():
        if normalized_logical_digest((ROOT / relative).read_text()) != expected:
            raise ValueError(f"Pinned logical target code changed in {relative}; re-audit target fidelity")
    return set(audited)


def check_output(output, expected, require_conditional_inputs=True):
    pattern = re.compile(
        r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
        re.MULTILINE,
    )
    results = pattern.findall(output)
    if Counter(name for name, _ in results) != Counter(expected):
        raise ValueError("Missing, duplicate, or unexpected axiom output")
    used = set()
    for name, axioms in results:
        dependencies = {value.strip() for value in axioms.split(",") if value.strip()}
        unexpected = dependencies - ALLOWED_AXIOMS
        if unexpected:
            raise ValueError(f"Unexpected axioms for {name}: {sorted(unexpected)}")
        used.update(dependencies)
    if require_conditional_inputs:
        for hypothesis in (
            "referencePreparation", "finiteCascade", "finiteConstruction",
        ):
            if not re.search(r"\(" + hypothesis + r"\s*:", output):
                raise ValueError(f"Main hypothesis not printed: {hypothesis}")
    return used


def main():
    if len(sys.argv) == 3 and sys.argv[1] == "--full-output":
        check_sources()
        used = check_output(Path(sys.argv[2]).read_text(),
                            {"EulerNonuniqueness.theorem11"}, False)
        print(f"Closed target proof checked; axioms: {', '.join(sorted(used))}.")
        return
    if len(sys.argv) != 2:
        raise ValueError("Usage: check_audit.py --source-only | build/axioms.txt | --full-output FILE")
    expected = check_sources()
    print(f"Source lint and explicit audit coverage pass: {len(expected)} theorem declarations.")
    if sys.argv[1] != "--source-only":
        used = check_output(Path(sys.argv[1]).read_text(), expected)
        print(f"Axiom allowlist passes: {', '.join(sorted(used))}.")
        print("Component audit only: this does not certify a closed proof of Theorem11.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError) as error:
        sys.exit(str(error))
