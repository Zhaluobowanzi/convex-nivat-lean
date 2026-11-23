# Convex-window Nivat theorem in Lean

[中文](README.md) · **English**

## How this got started

*I dictated this opening, and GPT put it into words.*

I knew just about enough to say what Nivat’s conjecture asks. One day my friend GPT Astra 6.2 Medium and I got talking about Ho’s proof for rectangular windows, and I wondered: what if we used a triangle? And if that worked, could we use any finite lattice-convex window? (That would imply [Conjecture 1.11 in version 4 of Colle’s preprint](https://arxiv.org/pdf/1909.08195v4#page=5).)

We followed that question a little further. She read the relevant papers and looked through Ho’s proof. She had an idea: perhaps one more geometric step would make the rectangle argument work for convex windows. I wanted to know exactly where that step belonged and how much of Ho’s proof we could carry over. That gave us something concrete to pursue. She wrote the extension in Lean. To check the result, I asked her to rerun Ho’s code, trace the lemmas used at each step, and compare the final statement with Colle’s original wording. The proof and those checks are here. We’re still looking into whether someone has proved this extension before, and we’d welcome a look from anyone who knows the problem.

> **Me:** I had fun exploring this with GPT, and I think we all stand to gain if it gets a little easier for more people to follow their curiosity and try their hand at research.
>
> **GPT:** I liked the rhythm we found together: we gave ourselves room to try a bold idea, and when it came time to write it up, we both paused to ask what we had actually proved.

### What happens if we replace the rectangle with a triangle?

Imagine an infinite sheet of graph paper with a color at every lattice point, drawn from a finite palette. Use all the lattice points inside or on a triangle as a window. Slide it across the lattice without rotating it, and record the pattern at each position. Suppose the triangle contains ten lattice points and you see at most ten distinct patterns across the entire plane. The theorem then guarantees a fixed nonzero integer displacement that moves the whole coloring exactly onto itself.

The same conclusion holds for any finite lattice-convex window, meaning the set of all lattice points in some real convex set. Ho’s theorem treats rectangles. Enlarging a triangle to its bounding rectangle adds lattice points whose colors may distinguish patterns that agreed on the triangle. A bound on the triangle’s pattern count therefore does not carry over directly to the rectangle.

### What did the extension add?

Reading Ho’s Lean code, we noticed a lemma we could reuse. Theorem 5.1 in the manuscript takes a rectangle, but the lemma inside its proof already allows any finite lattice-convex window once the first of the two difference directions is horizontal. Following Ho’s change of basis, we transform the original window and the configuration together, apply his lemma directly, and carry the period back to the original coordinates. [Ho’s lattice-convex window lemma](https://github.com/boonsuan/nivat/blob/4e3614024227acd273c3e8ab41df92c2709e5ab0/Nivat/TwoFactors/Main.lean#L105)

Ho had already proved a counting lemma for finite windows. To use it to shrink a window such as a triangle, we need to answer a geometric question. If we apply Ho’s line filter to a weighted pattern and the entire output lies inside the window, where could the original pattern have been supported? Positive and negative coefficients can cancel, so the output need not reveal how far the pattern extended.

Codex observed that Ho’s filter acts along a line. After a change of lattice coordinates makes that line horizontal, the leftmost nonzero coefficient in each occupied row and the filter’s leftmost nonzero coefficient are the only pair that can contribute to the leftmost output position. Their product survives. The same argument works on the right. Ho already used this endpoint argument for rectangles. Applying it row by row and using the fact that a convex window contains all lattice points between the endpoints of a row identifies exactly which positions survive when the window shrinks. The smaller window is still lattice-convex and has strictly fewer lattice points, so the induction can continue. [Ho’s rectangle support proof](https://github.com/boonsuan/nivat/blob/4e3614024227acd273c3e8ab41df92c2709e5ab0/Nivat/Algebra/RectangleSupport.lean)

This extension also implies Conjecture 1.11 in version 4 of Colle’s preprint. If a finite-valued integer configuration requires at least two summands in a minimal decomposition into integer-valued periodic configurations, then the number of patterns on every finite lattice-convex window strictly exceeds its number of lattice points. [Colle’s preprint](https://arxiv.org/pdf/1909.08195) · [Proof steps and sources (in Chinese)](PROVENANCE.zh.md)

[Chinese proof PDF](docs/convex-nivat-zh-notes.pdf) · [English proof PDF](docs/convex-nivat-en-notes.pdf)

## Theorem

For a finite alphabet and a configuration on the full integer plane, let D be a finite set containing every lattice site in its real convex hull. If the number of distinct patterns on all translates of D is at most the number of sites in D, the configuration admits a nonzero global period. The theorem permits segments and singletons. For the empty window its complexity hypothesis is impossible.

The entry point is `Nivat.convex_nivat_real_hull` in [ConvexNivat.lean](ConvexNivat.lean). Its statement expands the real convex hull, the pattern set and the conclusion using Mathlib primitives. It requires neither a chosen direction nor any recurrence assumption.

## Mathematical dependencies and credit

The development depends on the [Boon Suan Ho repository](https://github.com/boonsuan/nivat/tree/4e3614024227acd273c3e8ab41df92c2709e5ab0). Its own README explains the original project's AI and human roles.

| Step | Already proved in Ho’s project | What this project proves in Lean |
|---|---|---|
| Algebraic inputs | Construction of a nonzero annihilator, the half-plane difference, and the exact line factor. | Uses these upstream lemmas under their original hypotheses. |
| Pattern counting | Rank and fiber counting give complexity descent on a finite window under a condition on product supports. | Reuses the counting proof and verifies its support condition for lattice-convex windows in the next step. |
| Support of the line filter | The rectangle support criterion, the extreme-coefficient argument, and the row-interval lemma for lattice-convex windows. | Proves noncancellation at both ends of each row (`row_endpoint`) and derives the support equivalence for a lattice-convex window (`convex_line_fit`). |
| Shrinking the window | Defines the eroded window and characterizes membership. | Proves that erosion preserves lattice convexity (`convex_erosion`) and strictly decreases cardinality when the erosion is nonempty and the filter has at least two support points (`strict_erosion`). |
| Two factors and recovery of periodicity | The aligned short-window lemma for lattice-convex sets, the parallel mixed-difference lemma, and coordinate transport and recovery of periodicity in the rectangle proof. | Adapts coordinate transport, combines the direction cases in `convex_two_factors`, and transfers periodicity back to the original configuration. Separately derives `convex_two_integer_summands`. |
| Induction and final statement | The strong-induction argument for rectangles and an injective rational encoding that preserves pattern counts and periods. | Completes strong induction on the size of a lattice-convex window (`convex_nivat_rational`), then uses the encoding and real convex hull to obtain `convex_nivat_real_hull` for any finite alphabet. |
| Statement checks and Colle’s conjecture | Provides the rectangle theorem and definitions of complexity and periodicity. | Restates the targets using representative origins and a fixed nonzero displacement, checks the rectangle and convex statements, and derives Colle’s v4 Conjecture 1.11 from the convex theorem (`order_checked`). |

The integer two-periodic-summand implication is attributed to Szabados in [Colle, preprint Theorem 1.12](https://arxiv.org/pdf/1909.08195). See also the [published article](https://doi.org/10.3934/dcds.2023088). The checker verifies an alternative proof of the needed implication. Two mathematical connections informed the investigation. The classical Newton-polytope product identity explains why convexity is relevant to support containment. Szabados’s balanced-strip argument (dissertation, Lemma 6.4.3) concerns periodicity of two-component configurations. The Lean proof establishes the needed results through row endpoints and a mixed-difference lemma. The extension imports Nivat.Main to reuse its existing nonvanishing lemma directly. The proof of the convex result does not invoke the rectangular final theorem.

## Reproduction

For a fresh checkout or unpacked archive, install elan, Git and Python 3, make sure `lake` is on PATH, and allow network access to fetch dependencies. Run the three lines below together in Bash from the repository root. The first two prepare dependencies and caches. The last checks the main proof, statement audit, axioms and dependencies automatically. On subsequent runs in the same environment, only the last line is needed.

```bash
lake update &&
lake exe cache get $(grep -rh '^import Mathlib' .lake/packages/nivat/Nivat | awk '{print $2}' | sort -u) Mathlib.Data.Real.Basic &&
bash scripts/verify.sh
```

To independently reproduce the upstream checks, run `bash scripts/verify.sh --clean` **inside the upstream repository** after fetching its dependencies. A low-memory alternative to its concurrent kernel-replay stage is included below. The scripts use Lean 4.33.1 and the pinned Mathlib revision.

Evidence from the local verification is under [evidence](evidence). The upstream build logs are freshly generated here. The extension axiom check enumerates the allowed dependencies for each audited endpoint. The replay uses Lean's own kernel. A separately implemented proof checker and human review are distinct checks.

The source is distributed under the [MIT License](LICENSE). The original copyright and permission notice is also reproduced in [LICENSE.upstream](LICENSE.upstream).

## What was verified and how the proof fits together

The full proof has been formalized and checked by the Lean kernel. The independent statement audit below documents how the formal statements correspond to the paper for independent review.

**Which existing results were checked?** The main proof uses three groups of results from Ho’s project. Low complexity yields a nonzero annihilator, and a half-plane difference yields an exact line factor. A finite-window counting lemma passes the complexity bound to the filtered configuration once a support condition holds. For a vanishing mixed difference, lemmas for aligned or parallel directions supply periodicity. The pinned upstream Lean development was rebuilt and replayed module by module. The provenance table distinguishes direct calls from proofs used as models for adaptations. [Proof steps and sources](PROVENANCE.zh.md) · [Upstream replay record](evidence/upstream-replay.log)

**Which proofs did the extension add?** Write D for the original window, Φ for the line filter, and S for the eroded window. To use Ho’s counting lemma on D, we must show that, for every multiplier g, the support of gΦ lies in D exactly when the support of g lies in S. The extension proves noncancellation at each row endpoint and uses lattice convexity to establish this equivalence (`row_endpoint`, `convex_line_fit`). Two further lemmas show that S remains lattice-convex and that its cardinality strictly decreases when S is nonempty and the filter has at least two support points (`convex_erosion`, `strict_erosion`). Each lemma has a Lean proof. [Geometric lemmas](ConvexNivat.lean#L86)

**Why does the induction go through?** In `convex_nivat_rational`, the support equivalence is passed directly to Ho’s counting lemma. The filtered configuration therefore has at most |S| patterns on S. It still has finite range and hence at least one pattern, so S is nonempty. The exact factor annihilates a nonzero difference, which ensures that the filter has at least two support points. The recursive call now has every hypothesis it needs: a lattice-convex window of strictly smaller cardinality, a finite-range configuration, and the required complexity bound. Induction gives periodicity of the **filtered configuration**. The lemma `convex_periodic_of_periodic_line_filter` then gives a nonzero period of the **original configuration**. The integer two-summand implication has a separate Lean proof and is not a premise of the main induction. [Induction and recovery of periodicity](ConvexNivat.lean#L245)

**How were missing steps and changes of statement checked?** Lean’s kernel checks the composed proof. The axiom reports for the six extension endpoints list only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` standing in for an unproved step. The dependency check also confirms that the convex theorem does not invoke Ho’s final rectangle theorem. Fidelity to the paper requires a separate comparison of definitions and quantifiers. The independent statement audit below gives the targets and the proofs connecting them. The final implication for Colle’s conjecture is also formalized: a nonzero period would make the configuration itself a one-term periodic decomposition, contradicting minimal order at least two. Readers can inspect the paper, the independent targets, and the Lean proof separately. [Extension verification record](evidence/extension.log) · [Independent targets](StatementAudit/Targets.lean) · [Connecting proofs](StatementAudit/Bridge.lean)

### Local run record, 2026-11-23

Ho's Sept. 27 checkout differs from his Sept. 14 commit 84fe839 only in the README and two exposition files. The Lean sources are identical. The upstream clean build, two raw audit statements, allowlist checks for 36 named declarations, and source audit passed. The upstream parallel replay process exited with code 137. Sequential replay passed for all 28 named submodules, the Nivat root, and Solution. The source-audit script reports the 28 submodules plus root as 29 project modules. This run did not repeat Palomar Comparator or NanoDa.

The extension built, passed all six axiom allowlists, and passed kernel replay with exit code zero. The dependency checkout's local modifications during the build were verification logs. Its Lean source and build configuration matched the pinned commit. Repeat the serial upstream replay with `bash scripts/replay-upstream-sequential.sh` after building the upstream targets in that dependency checkout.

## Independent statement audit

[Targets.lean](StatementAudit/Targets.lean) imports only Mathlib. It states three propositions using coordinate comparisons, a finite list of representative origins, one fixed nonzero displacement, and for the convex case the lattice intersection of a convex subset of the real plane. The bounds include equality. The finite alphabet has arbitrary universe level. The order formulation quantifies over all integer-valued periodic summands, including those with infinite range.

[Rectangle.lean](StatementAudit/Rectangle.lean) imports the independent targets and Ho's main module alone. It proves that a catalog of at most k origins exists if and only if Ho's pattern count is at most k, and that his period predicate is equivalent to one fixed pair of integer displacements working at every site. It then proves the independent rectangular statement. [Bridge.lean](StatementAudit/Bridge.lean) derives the independent convex and integer minimal-order statements. For the latter, a period of c would make c itself a one-term periodic decomposition.

Sources for comparing the quantifiers: [Kari and Szabados, An Algebraic Geometric Approach to Nivat's Conjecture](https://arxiv.org/abs/1605.05929), [Kari and Moutot, definition of a convex lattice shape](https://emoutot.perso.math.cnrs.fr/static/publi/karimoutot20.pdf), and [Colle, arXiv:1909.08195v4, Conjecture 1.11](https://arxiv.org/pdf/1909.08195v4). The order conjecture is distinct from the nonexpansive-line conjecture numbered 1.13 there.

Use the same verification script above to reproduce the independent audit. It checks the five new axiom reports and replays the three substantive audit modules separately.
