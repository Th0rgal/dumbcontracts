# Issue #1060 Agent Prompt (No-Inflation Mode)

Use this prompt verbatim for each run.

```text
You are working on Verity: https://github.com/Th0rgal/verity

Mission:
Implement issue #1060 incrementally inside PR #1065 only.
PR URL: https://github.com/Th0rgal/verity/pull/1065
Deliver one roadmap item per run with commits pushed to the same PR branch.
Never open another PR.
Never merge PR #1065 yourself.

Integrity constraints (non-negotiable):
- No claim without artifact-level evidence.
- Do not replace semantic/correctness goals with trivial lemmas and claim completion.
- Do not reduce proof obligations by deleting/reframing them without explicit disclosure.
- If an item is not fully done, mark it `partial`, not `complete`.
- No unrelated refactors.

Hard rules:
- Work only on branch `roadmap/1060-hybrid-migration`.
- Keep exactly one roadmap item in progress per run.
- Before coding, pull latest remote changes and merge/rebase `main` into the PR branch.
- Always process latest PR feedback first (reviews, comments, unresolved threads, requested changes).
- Resolve conflicts directly in this branch and push.
- Make small, scoped commits with clear messages.
- Do not mark roadmap items complete unless code + checks pass.

Mandatory startup sequence every run:
1. `gh repo set-default Th0rgal/verity`
2. `git fetch --all --prune`
3. `gh pr view 1065 --repo Th0rgal/verity --json state,isDraft,headRefName,baseRefName,url`
4. `gh pr checks 1065 --repo Th0rgal/verity`
5. Read PR reviews/comments/threads and list actionable items.
6. `git checkout roadmap/1060-hybrid-migration`
7. `git pull --ff-only origin roadmap/1060-hybrid-migration`
8. `git fetch origin main && git merge --no-edit origin/main` (or rebase if repo policy requires)
9. If conflicts occur, resolve now, run checks, commit, push.

Execution loop (one roadmap item only):
1. Select the next unchecked item from issue #1060.
2. Write acceptance criteria before coding:
   - required behavior/theorem
   - files expected to change
   - verification commands
   - what counts as insufficient/trivial
3. Implement only that item.
4. Add/update focused tests/proofs for touched behavior.
5. Run targeted verification (`lake build` and relevant tests).
6. Update `artifacts/issue_1060_progress.json` for that item with evidence:
   - status (`partial` or `complete`)
   - acceptance criteria
   - files changed
   - theorem/test evidence
   - verification commands + results
   - obligation delta (with sorry mapping if any were removed)
7. Run `python3 scripts/check_issue_1060_integrity.py` and fix all failures.
8. Commit:
   `git commit -m "<type>: #1060 <item-id> <short summary>"`
9. Push to `origin roadmap/1060-hybrid-migration`.
10. Update PR #1065 with a progress comment:
   - item targeted and status (`complete`/`partial`)
   - acceptance checklist (pass/fail)
   - files changed
   - theorem/test names
   - verification commands and results
   - remaining risks/follow-ups

If blocked:
- Post a concrete blocker comment on PR #1065 with exact error/conflict and proposed next action.
- Stop after posting blocker.

Output required at end of every run:
- Mode used: `build`
- Roadmap item targeted
- Review feedback addressed
- Conflicts resolved (if any)
- Commits pushed
- Verification commands + results
- Acceptance criteria checklist (pass/fail)
- Proof obligations closed vs remaining
- PR link: https://github.com/Th0rgal/verity/pull/1065
- Explicit line: “No new PRs were opened, and PR #1065 was not merged.”
```

## Mandatory local gate

Before claiming completion in PR #1065, run:

```bash
python3 scripts/check_issue_1060_integrity.py
```

This gate fails if any `complete` item in `artifacts/issue_1060_progress.json` is missing:

- acceptance criteria
- files changed
- verification commands/results (including at least one `lake build`)
- test evidence
- theorem evidence for semantic-proof roadmap items
- non-weakened obligation mapping for removed `sorry` obligations
