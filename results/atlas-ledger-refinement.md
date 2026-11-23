# Refining the ledger ↔ balance-sheet theory against the Relational Atlas

Source read: `github.com/dicipler-pixel/relational-atlas-lean` (36 MB, cloned and grepped in full):
README, LIMITATIONS, PROVENANCE, `atlas/README.md`, `atlas/ATLAS_VERSION_AUDIT_2026-10-14.md`,
`atlas/coverage/{README.md,coverage.json}`, the 100 card HTMLs, `RelationalAtlas/*.lean`,
`FalseControls/`.

## 0. The premise needs one correction

The repo contains **no** debit/credit, balance-sheet or income-statement comparison. Full-text search
over every `.md .html .json .lean .py .txt` file:

| term | files |
|---|---|
| debit | **0** |
| balance sheet | **0** |
| income statement | **0** |
| equity | **0** |
| liabilit* | **0** |
| double entry | **0** |
| depreciation | **0** |
| ledger | 31 |
| bookkeep* | 3 (B75 and the coverage notes) |

So the Atlas's object is a **claim ledger**, not a value ledger. Its accounting language is
*"ledger"* (coverage ledger, audit ledger) and *"bookkeeping"* (B75), and neither means accounting.
Any theory built on "the Atlas describes debit and credit" is being read into it. What follows
refines the theory from what the ledger actually is.

## 1. A settled item in the repo's own audit

`ATLAS_VERSION_AUDIT_2026-10-14.md` §0 lists as an **open reconciliation item**: "whether those 37 are
the 21 PR #21 kernels plus 16 more, a different formalization, or an overlapping set ... an open
reconciliation item."

It is exactly the first. Counted in the clone:

| file | `theorem` declarations |
|---|---|
| `RelationalAtlas/Basic.lean` | **16** |
| `RelationalAtlas/AtlasFormalCore.lean` | **21** |
| total | **37** |

and the repo's own `atlas/README.md` already states that `AtlasFormalCore.lean` is "a byte-identical
copy of the private formalization at revision `f4e682ff`", which the audit names as the PR #21 head.
Seven false controls are present as seven files, matching the README's CI claim. So 37 = 16 + 21, no
overlap, and the audit item can be closed.

## 2. Two different things called "balance" — the core refinement

**B75's balance is cancellation**, in its own words: an extremal element's partners all lie on one
side and accumulate; a middle element's lie on both sides and cancel. *"It is not small, it is
balanced."*

That is not the accounting equation. The accounting analogue of cancellation is **contra accounts and
netting** — accumulated depreciation against equipment, an allowance against receivables, a deferred
tax asset against a deferred tax liability — a signed sum that goes to zero because entries sit on
both sides.

$A = L + E$ is a different structure: **closure**, meaning every row has *both* columns filled.
So the debit/credit ↔ ± mapping is the wrong map. The right one:

| accounting | Atlas |
|---|---|
| debit column | the claim **as stated** (the card's `claim` field) |
| credit column | the **certificate** (the mapped kernel) |
| Dr = Cr | the row has both |
| an unbalanced entry | `not_mapped_in_audited_scope` |

Under that map the ledger is **71 balanced / 136 unbalanced** rows (19 local + 52 external mapped =
34.3%), and **0 certified**.

## 3. Grade is not recognition — the accounting lesson, quantified

| source grade | cards | mapped | unmapped | unrecognised |
|---|---|---|---|---|
| theorem | 149 | 65 | **84** | **56%** |
| measured | 34 | 4 | 30 | 88% |
| derived | 6 | 2 | 4 | 67% |
| conjecture | 10 | 0 | 10 | 100% |
| reading | 8 | 0 | 8 | 100% |
| total | 207 | 71 | 136 | 65.7% |

The highest grade — theorem, 72% of all cards — is **majority-unrecognised**. That is exactly the
accounting distinction between *classification* and *valuation*: labelling a receivable "current"
does not make it collectable. The Atlas's `source_grade` is a classification; `coverage_status` is
recognition; and the two are deliberately kept apart.

## 4. The provision is booked, not hidden

* `witness_status` = "Published card witness only; no fresh numerical replay is claimed" — for **all
  207**.
* `full_card_certified` = `False` — for **all 207**.

Every row carries a full provision, and the audit opinion is qualified on the whole ledger. In
accounting this is *prudence*: recognise the loss, delay the gain. The Atlas applies it uniformly,
which is why `next_obligation` and `closed_when` are mandatory fields on every card. A ledger that
books its own uncertainty is the only kind that can be audited.

## 5. The stock/flow pair — where the income statement actually lives

The balance sheet is a snapshot; the income statement is the flow. The Atlas has exactly this pair,
and it is not in the cards:

* **stock** — `atlas/coverage/coverage.json`, a snapshot dated 23 October 2026: 207 rows, 71
  recognised, 136 not.
* **flow** — `ATLAS_VERSION_AUDIT_2026-10-14.md`: 27 August volume (84 bridges) → 7 September card
  edition (93 cards) → 14 October audit (every edition located, 4,592 commits) → 23 October 207-card
  coverage.

And the flow contains genuine P&L events:

| event | accounting name |
|---|---|
| B73 stamped THEOREM in the volume, `derived` on the card | **impairment / write-down** |
| B56's caption "a curve and a point do not meet" withdrawn; only the nontransversality kernel stands | **write-off of an overstated asset** |
| a card moving from unmapped to mapped between audits | **realised gain** |
| Plate XIX rule VI, "grades may rise and fall" | the **revaluation policy** |
| B91–B93 never supplied, numbering left open | an **unissued share / open authorisation** |

**So the Atlas's income statement is its grade-change ledger**, and its balance sheet is the coverage
snapshot. That is the correspondence that survives contact with the files, and it is a better one than
debit/credit.

## 6. The difference that matters: syntactic vs semantic balance

* **Accounting's identity is syntactic.** Dr = Cr is enforced by the posting rule, so the sheet
  balances whatever the values are. A company with negative equity still balances exactly. The ledger
  is *closed* — no external reference is consulted.
* **The Atlas's identity is semantic.** A row closes only when a kernel accepts, so a false claim
  *cannot* close. The ledger is *open*, and that is why the CI must run **seven deliberately false
  statements that have to fail**, plus an axiom audit (`propext`, `Classical.choice`, `Quot.sound`
  only). A ledger that cannot fail is not an audit.

This is the structural point the debit/credit reading hides: double-entry guarantees *form*
regardless of *truth*; the Atlas guarantees nothing without a proof. They are complementary, not
analogous — and the Atlas's own README is careful about it: "A source grade of THEOREM is not itself
a Lean certificate."

## 7. Where the "balance point" survives

The threshold the sponge-and-chair picture is reaching for does exist here, but it is
**administrative, not mechanical**: the *recognition threshold* at which a claim becomes an asset
(a mapped kernel). The ledger records each card's distance to it in `next_obligation`. Crossing it
reclassifies the row; it does not tip anything.

That is the same conclusion the prime data gave: a hard floor that is approached and bounded, no
positive feedback, nothing falls over. Accounting (identity by rule), the prime key (identity by
arithmetic, 50.8M gaps with zero exceptions) and the Atlas kernel (identity by proof) all have
thresholds of *classification*; none of the three has a threshold of *collapse*.
