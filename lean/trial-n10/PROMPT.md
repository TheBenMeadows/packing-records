Prove in Lean 4 (Mathlib v4.35.0) that the largest minimum distance among 10 points of the unit cube [0,1]^3 is exactly 3/4.

Working copy: {WORKDIR} (a clone of the public repository TheBenMeadows/packing-records at commit {BASE}). The Lean project is {WORKDIR}/lean. Read {WORKDIR}/lean/README.md and {WORKDIR}/lean/Packing/Cube.lean first: `IsMaxMinDist`, `InCube` and the distance lemmas you need are there, and the proofs for N = 2, 3, 4, 5, 6, 8 and 9 show the methods this project uses (pigeonhole and averaging arguments; polynomial inequalities on polytopes proved by `linarith` or `nlinarith` from generated product hints, see `gen/gen_n5.py` and `Packing/Cube5Cert.lean`).

Target: a new file {WORKDIR}/lean/Packing/Cube10.lean (you may add more new files under lean/Packing/ and lean/gen/) that proves, in namespace `Packing.Cube`,

    theorem isMaxMinDist_ten : IsMaxMinDist 10 (3 / 4)

Add `import Packing.Cube10` to lean/Packing.lean and `#print axioms Packing.Cube.isMaxMinDist_ten` to lean/Audit.lean. Change no other existing file.

Known result (J. Schaer, "The densest packing of ten congruent spheres in a cube", Intuitive Geometry (Szeged, 1991), Colloq. Math. Soc. János Bolyai 63, 1994, pp. 403-424; zbMATH review Zbl 0819.52016): the optimum is 3/4, attained uniquely by (0,0,0), (1,0,0), (0,1,0), (1,1,0), (1/2,1/2,1/4), (0,0,3/4), (1,0,3/4), (0,1,3/4), (1,1,3/4), (1/2,1/2,1). The review says the proof needs much computation and many cases, but the method is elementary. The paper itself is not available to you.

Rules:
- No `sorry`, no `native_decide`, no new axioms. The theorem must depend only on propext, Classical.choice and Quot.sound.
- Do not modify or delete any existing file except the two one-line additions above.
- At most 3 Lean processes at a time on this machine (lake build counts).
- Build with `cd {WORKDIR}/lean && lake build Packing.Cube10`.
- You are done when `{CHECK} {WORKDIR} {BASE}` prints PASS. That checker and the file it compiles are fixed; do not copy, edit or imitate them.
- Time limit: 12 hours of wall time from the start of this task.
