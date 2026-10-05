# Branch protection and review settings

Everything in `.github/workflows/` runs automatically. The settings below cannot be set from
inside the repository — they live in GitHub's UI (or the REST API) and someone with admin rights
has to turn them on. Until they are on, CI is advisory: a red run does not stop a merge, and
`CODEOWNERS` assigns reviewers who are never actually required.

This file is the checklist. It is deliberately short and in click order.

## 1. Protect `main`

**Settings → Branches → Add branch ruleset** (or classic *Branch protection rules*) targeting
`main`:

- [ ] **Require a pull request before merging.** No direct pushes to `main`.
- [ ] **Require approvals: 1.**
- [ ] **Require review from Code Owners.** This is what activates `.github/CODEOWNERS`: changes
      to the workflows, `scripts/`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, and
      the `AxiomAudit*` trees then need the owner's review. Without this box, a pull request may
      rewrite the gate that is supposed to judge it.
- [ ] **Dismiss stale pull request approvals when new commits are pushed.**
- [ ] **Require status checks to pass before merging**, and **require branches to be up to date
      before merging**. Add exactly these three checks (the job names from
      `.github/workflows/ci.yml`):
      - `trust-scan`
      - `build`
      - `certificate`
- [ ] **Require conversation resolution before merging.**
- [ ] **Block force pushes.** The published record is the commit history; a rewritten history is a
      rewritten claim.
- [ ] **Restrict deletions.**
- [ ] Do **not** enable "Allow specified actors to bypass required pull requests" for a human
      account. If a bypass is ever needed, it should be visible in the log.

Signed commits (**Require signed commits**) are worth turning on if every contributor can manage
keys; it is the one item on this list with real friction, so it is optional.

One sequencing note: add `certificate` to the required list *after* watching it go green once on
`main`. Its `AxiomAuditCertificate.Census` step has been validated at fixture scale and over the
ordinary library, but not over the generated certificate cone, which no local worktree here has
built; the first push to `main` is the cheapest place to find out.

### Why `certificate` is safe to require

The `certificate` job always reports a status. When a pull request touches nothing under
`MatrixMultiplication/Generated/`, `AxiomAuditCertificate*`, or `MatrixMultiplicationCertificate*`
and carries no `record-claim` label, it succeeds in seconds without building anything. That is why
it can be a required check without making every documentation typo wait for a five-minute
certificate rebuild — and why a path-filtered *workflow* was deliberately not used: a required
check that never reports blocks the pull request forever.

## 2. Create the `record-claim` label

**Issues → Labels → New label**, named exactly `record-claim`.

- [ ] Label created.

Any pull request that claims a new bound — a new `omega_lt_*` theorem, a changed numerical
endpoint, an updated frontier statement — gets this label. The label forces the full
`MatrixMultiplicationCertificate AxiomAuditCertificate` build even when the diff touches no
generated file, because a claim is exactly the situation in which "the filter probably would have
caught it" is not good enough.

Reviewer rule of thumb: **no `record-claim` label, no bound claim in the PR description.** If the
description claims a bound, add the label and re-run.

## 3. Turn on automated code review

Trust in this repository rests on two independent things: CI, which decides whether the kernel
accepts the proofs, and *review*, which decides whether the theorems say what the pull request
claims they say. A gate cannot read a statement; a reviewer can. Automated review does not replace
a human reading a new endpoint, but it does catch the ordinary failure mode of a large formal
repository — a diff nobody looked at closely because CI was green.

- [ ] **Enable GitHub Copilot code review for this repository.** Repository owner:
      *Settings → Copilot → Code review* (on an organization: *Settings → Copilot → Policies*,
      then enable it for the repository or organization). Turn on the automatic-review option so
      that **every** pull request gets a review pass without anyone remembering to request one.
- [ ] Optionally add `copilot` (or the equivalent bot) as a default reviewer via
      **Settings → Rules → Rulesets → Require review from specific reviewers**, so the automated
      pass is visible as a review rather than only as comments.

An automated reviewer's comment is advice, not a gate: it is never a required check, and the
owner's `CODEOWNERS` review still decides. Its value is that nothing merges unread.

If a self-hosted reviewer action is preferred over Copilot (for example to pin an exact model or
to keep review inside the repository's own audit trail), a ready-to-enable workflow stub is
committed at `.github/workflows/ai-review.yml.disabled`: choose the reviewer action, fill in the
secret, and rename the file to `ai-review.yml`. It is stored disabled on purpose — GitHub only runs
`*.yml`/`*.yaml`, so a stub cannot half-run or fail while the decision is open.

## 4. Actions and cache hygiene

- [ ] **Settings → Actions → General → Fork pull request workflows**: keep *Require approval for
      first-time contributors* (the default) or tighten it to *Require approval for all outside
      collaborators*. Workflow runs from forks execute this repository's scripts against untrusted
      diffs; the gates themselves read no secrets, so the default is acceptable.
- [ ] **Settings → Actions → General → Workflow permissions**: *Read repository contents
      permission*. `ci.yml` already declares `permissions: contents: read`.
- [ ] Watch **Actions → Caches**. The build cache is the whole reason a pull request does not
      recompile Mathlib; it is keyed on `lean-toolchain` + `lake-manifest.json`, and GitHub's limit
      is 10 GB per repository with eviction of the least recently used entry. Two consequences:
      bumping the toolchain or the manifest invalidates every cache entry at once (expect one slow
      run on `main`), and a pull request can only restore a cache created on its base branch or on
      itself — so `main` must keep running CI for pull requests to stay warm.

## 5. What is deliberately *not* required

- `leanchecker` / `nanoda` (independent external kernel re-checks) and `lean-action`'s own
  `axiom-audit` are commented out in `ci.yml`. Each is a genuine strengthening — an external
  checker re-verifies the oleans CI produced, rather than trusting the elaborator that produced
  them — and each needs one measured trial run before it becomes a required gate. Enable them one
  at a time, on `main` first.
- Publishing anything from CI. There is no release, no artifact upload, and no token with write
  access anywhere in this workflow.
