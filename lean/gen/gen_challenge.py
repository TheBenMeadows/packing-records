"""Write Challenge/*.lean, the trusted statements that `lake comparator` judges the library against.

For each module imported by Packing.lean, in order, the challenge module keeps the file's context
lines (imports, namespace, open, variable, set_option), copies verbatim every definition that a
statement needs (found by name, transitively), and states each theorem listed in Audit.lean with
`sorry` as its proof. Challenge/Cert/Cells.lean (the sampled record cells) is written by hand.

  python3 -I gen/gen_challenge.py           write Challenge/ and Challenge.lean
  python3 -I gen/gen_challenge.py --check   exit 1 if the files on disk differ from a fresh run

The output is meant to be read: a definition copied here is what the theorems are about.
"""
import re, sys, pathlib, tempfile, filecmp
root = pathlib.Path(__file__).resolve().parent.parent
CHECK = sys.argv[1:] == ['--check']
out = pathlib.Path(tempfile.mkdtemp()) / 'Challenge' if CHECK else root / 'Challenge'
extra = []
# Definitions that no statement names but that must precede one that does: the elaborator gave
# Packing.Cube5.T an auxiliary proof that the value of Packing.Cube5.five reuses.
FORCE = {'cd', 'T'}
FORCE_MODULE = 'Packing.Cube5'
names = [l.split()[-1] for l in (root/"Audit.lean").read_text().splitlines() if l.startswith("#print axioms")]
order = [l.split()[1] for l in (root/"Packing.lean").read_text().splitlines() if l.startswith("import ")]
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected|partial|unsafe|nonrec)\s+)*(theorem|lemma|def|abbrev|structure|class|inductive|instance|example|opaque|axiom)\b\s*([^\s:({\[]*)")
CTX = re.compile(r"^(namespace|end|section|open|variable|universe|set_option|noncomputable section|local notation|notation|scoped|attribute|local instance|macro|syntax)\b")
files = {}
for mod in order:
    p = root/(mod.replace(".", "/") + ".lean")
    lines = p.read_text().splitlines()
    blocks = []  # (kind, name, start, end)
    i = 0; starts = []
    for n, l in enumerate(lines):
        m = DECL.match(l)
        if m: starts.append((n, m.group(1), m.group(2)))
        elif CTX.match(l) or l.startswith("import "): starts.append((n, "ctx", l))
    starts.append((len(lines), "eof", ""))
    for a, b in zip(starts, starts[1:]):
        # pull preceding docstring/attribute lines into the block start
        blocks.append((a[1], a[2], a[0], b[0]))
    files[mod] = (lines, blocks)
# all definitions in library
defs = {}
for mod, (lines, blocks) in files.items():
    for kind, name, s, e in blocks:
        if kind in ("def", "abbrev", "structure", "class", "inductive", "instance", "opaque"):
            defs.setdefault(name.split(".")[-1], []).append((mod, s, e, kind, name))
want_thm = {n.split(".")[-1] for n in names} | {n.split(".")[-1] for n in extra}
# closure of needed defs from statement texts
def stmt_text(lines, s, e):
    t = "\n".join(lines[s:e]); return t.split(":=")[0]
need = set(); frontier = []
for mod, (lines, blocks) in files.items():
    for kind, name, s, e in blocks:
        if kind in ("theorem", "lemma") and name in want_thm:
            frontier.append(stmt_text(lines, s, e))
tok = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
while frontier:
    t = frontier.pop()
    for w in set(tok.findall(t)):
        for cand in {w, w.split(".")[-1]}:
            if cand in defs and cand not in need:
                need.add(cand)
                for mod, s, e, kind, name in defs[cand]:
                    frontier.append("\n".join(files[mod][0][s:e]))
natural = set(need)
out.mkdir(parents=True, exist_ok=True)
mods = []
for mod, (lines, blocks) in files.items():
    body = []; useful = False
    for kind, name, s, e in blocks:
        chunk = lines[s:e]
        if kind == "ctx":
            l = chunk[0]
            if l.startswith("import "):
                if l.split()[1].startswith("Packing."):
                    body.append("import " + l.split()[1].replace("Packing.", "Challenge.", 1))
                else: body.append(l)
            else: body.append(l)
            # keep continuation lines of multi-line variable/open
            for c in chunk[1:]:
                if c.startswith((" ", "\t")) and l.startswith(("variable", "open")): body.append(c)
                else: break
        elif kind in ("def", "abbrev", "structure", "class", "inductive", "instance", "opaque") and (name.split(".")[-1] in natural
                 or (name.split(".")[-1] in FORCE and mod == FORCE_MODULE)):
            if name.split(".")[-1] in FORCE and name.split(".")[-1] not in natural and mod == FORCE_MODULE \
                    and not any("auxiliary proof" in b for b in body):
                body += ["-- Not named by any statement: the value of `five` reuses an auxiliary proof that",
                         "-- the elaborator generated for `T`, so `cd` and `T` must precede `five` here."]
            if "private" in chunk[0]: print("PRIVATE needed:", mod, name, file=sys.stderr)
            body += chunk; useful = True
        elif kind in ("theorem", "lemma") and name in want_thm:
            t = "\n".join(chunk); head = t.split(":=")[0].rstrip()
            body.append(head + " := by\n  sorry\n"); useful = True
    target = out/(mod.replace("Packing.", "", 1).replace(".", "/") + ".lean")
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text("\n".join(body) + "\n")
    mods.append(mod.replace("Packing.", "Challenge.", 1))
(out.parent/"Challenge.lean").write_text("\n".join("import " + m for m in mods + ["Challenge.Cert.Cells"]) + "\n")

# Drop docstrings whose next non-blank line does not start a declaration (their declaration was not kept).
START = re.compile(r"^(?:@\[|noncomputable def|noncomputable abbrev|def |abbrev |theorem |lemma |structure |class |inductive |instance |private |protected )")
for f in out.rglob("*.lean"):
    ls = f.read_text().splitlines(); res = []; i = 0
    while i < len(ls):
        if ls[i].lstrip().startswith("/--"):
            j = i
            while "-/" not in ls[j]: j += 1
            k = j + 1
            while k < len(ls) and not ls[k].strip(): k += 1
            if k < len(ls) and START.match(ls[k]): res += ls[i:j + 1]
            i = j + 1; continue
        res.append(ls[i]); i += 1
    f.write_text("\n".join(res) + "\n")

if CHECK:
    import os
    real = root / 'Challenge'
    bad = []
    for f in out.rglob('*.lean'):
        g = real / f.relative_to(out)
        if not g.exists() or f.read_text() != g.read_text():
            bad.append(str(f.relative_to(out)))
    if (out.parent / 'Challenge.lean').read_text() != (root / 'Challenge.lean').read_text():
        bad.append('Challenge.lean')
    if bad:
        print('differs from a fresh run:', ' '.join(bad)); sys.exit(1)
    print('Challenge/ matches a fresh run')
