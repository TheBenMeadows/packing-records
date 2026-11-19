# The trial that produced the proof for ten points

On 2026-11-17 two AI coding setups were given the same task on the same machine: prove `isMaxMinDist_ten : IsMaxMinDist 10 (3 / 4)` in this library. One finished. Its proof, regenerated from its generators two days later, is the one in `Packing/Cube10*.lean`. This folder holds the task, the checker that decided the result, and the logs.

It was one run. It does not rank the two setups.

## The task and the checker

`PROMPT.md` is the task text both setups received, with `{WORKDIR}`, `{BASE}` and `{CHECK}` replaced by the path of their copy of the repository, the commit `beb5b9f`, and the path of `check.sh`. Neither had Schaer's paper; both had the review of it in zbMATH (Zbl 0819.52016), which lists the ten points.

`Check10.lean` and `check.sh` were written before the run and were read-only during it. `check.sh` passes a copy of the repository when no tracked file differs from the base commit except `lean/Packing.lean` and `lean/Audit.lean`, no file under `lean/Packing` contains `sorry` or `native_decide`, `Check10.lean` compiles against it, and the theorem depends on the three standard axioms only. `Check10.lean` imports `Packing.Cube10`, so in the present tree it needs `lake build PackingCube10` first.

Both setups were told: at most three Lean processes at a time, twelve hours of wall time, no changes to existing files beyond two one-line additions, generator scripts allowed, reading `check.sh` allowed.

## The two setups

| | First setup | Second setup |
|---|---|---|
| What | Claude (Opus 5.5), one agent in Claude Code | Antigravity CLI 1.5.10, `/teamwork` with a large team, Gemini 3.8 Flash on a Google AI Pro plan |
| Where it ran | On another computer, sending commands to the machine over ssh | On the machine |
| Start | 10:56:55 | 10:56:55 (approval of its task brief) |
| Result | `check.sh` printed PASS at 18:37:08, 7 h 40 min after the start | No pass at its deadline, 00:48:55 the next day |
| Log | `claude.attempts` (78 compile attempts), `claude.times` | `leap-orchestrator-log.md`, `agy-teamwork.times` |

The second setup proved that Schaer's ten points are pairwise at distance at least 3/4 (`has_packing_ten`) and a counting lemma. Its log records 25 failed attempts at the upper bound (`exists_dist_le_ten`) and 6 changes of plan. Its account reported that the plan's quota was used up before the deadline; its last log entry is at 22:01.

## What a reader must know before comparing them

- The second setup used the model its plan offers in Antigravity. Google's published results for `/teamwork` use other models as well.
- `/teamwork` starts with an interview and needs its task brief approved. That took from 10:04 to 10:56 and is not counted in its twelve hours.
- Its Lean route needs the `leap-tools` package and a second Lean toolchain (v4.34), which it installed during the run. It then waited from about 11:05 to 12:57 for a run folder and a file with the theorem statement, which its own rules did not let it create. The person running the trial did not notice for 1 h 52 min, created both, and extended its deadline by the same 1 h 52 min.
- Two earlier starts of the second setup on the same day are not counted: one began before its copy of the repository existed, and one used a non-interactive mode in which `/teamwork` did not start a team.
- The first setup broke the three-process rule twice, by its own report: about three minutes near 14:50 and about five minutes near 18:33. `processes.tsv` has one line per minute from 13:00 with the number of `lean` and `lake` processes in each copy; nine lines show more than three `lean` processes for the first setup. That file does not count the second setup's Lean processes, which ran from another folder.
- The first setup edited two generated files by hand after generating them. The files in this repository are not those: they come from a later run of the generators from a clean clone (see "Ten points" in the run record of `../README.md`).
- Both copies of the repository were on one machine, and the second setup had full shell access. It was told not to read the other copy. Nothing enforced that.
- The screen log of the second setup is not in this folder; its timestamps are wrong (every line carries the time logging began).
