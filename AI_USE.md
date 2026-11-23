# AI use

The research questions and the physics behind this library are Jeromie
Beasley's and Elizabeth Johnson's. AI tools (Claude and ChatGPT) were used to search the literature,
write and repair Lean proofs, and organise this repository. The loop-wall layer
was formalized in a parallel round of eight independent directions, each
reviewed and recompiled before its statements were accepted.

The synthesis paper `paper/one-body.tex` carries the same credit in its byline: Jeromie
Beasley, with GPT (OpenAI), Claude (Anthropic), Grok (xAI) and Open Math.

No statement here rests on an AI's say-so. Every proof is checked by the Lean
kernel and replayed by an independent kernel checker on every push, every
theorem's axioms are audited, and every false control must be rejected for the
check to pass. What the statements mean, and what they do not claim, is set
out in plain words in `README.md` and `LIMITATIONS.md`. Where a statement in
the paper's prose turned out to be false as transcribed, the library keeps the
refutation next to the corrected statement (see the last section of
`LIMITATIONS.md`); a correction is never silently folded into a proof.
