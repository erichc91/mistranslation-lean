# The MEMS pull-in number is transcendental

A MEMS switch is a thin plate pinned above an electrode. Push it too hard and it snaps down. The largest push that
still works, about 1.4000165, has been computed numerically for a long time. This repo proves in Lean 4, starting
from the equation itself, that this number exists and is transcendental (no polynomial with whole-number
coefficients has it as a root).

```lean
theorem mems_pull_in_transcendental :
    ∃ B : ℝ, IsGreatest {μ | ∃ v v' : ℝ → ℝ, MemsOde.Sol μ v v'} B ∧ Transcendental ℚ B
```

`MemsOde.Sol μ v v'` says: `v'' = μ / v²`, `v > 0` on [0, 1], `v(0) = v(1) = 1`.

## Everything else in here

`Mistranslation/Table.lean` lists 67 results, one line each, and prints a receipt for every one. Every receipt says
`propext, Classical.choice, Quot.sound` and nothing else. Among them:

- **The law** (`Recipe.transcendental_of_recipe`): when a polynomial balance and an exponential clock are forced to
  agree at one point, and the clock enters linearly, the meeting value is transcendental.
- **The MEMS pull-in ladder** and the **flame equation (Bratu)**: break numbers transcendental, from the equation.
- **A predicted family** (`v'' = μ cosh v / sinh³ v`): one theorem gives a new transcendental break for every
  algebraic boundary value, so infinitely many. `InfinitelyMany.certified_infinite` proves the law certifies infinitely many transcendental breaks.
- **Bridges** (Kepler, Morse, K₃, P₃, P₅): whole families sliding between known break numbers, every point classified.
- **The circle clock** (springs, `π²`, `(w/sin w)²`): settled by Lindemann's theorem for sine.
- **The pinch** (`x'' + μ(1 + x + λx²) = 0`): the first number closed inside a family that was otherwise open.
  At λ* (between 0.0755 and 0.0756) the break exists and is transcendental (`PinchMax.break_lam_star`).
- **Seats with no break at all**, and the rule for when that happens.

The table this came from had 260 seats; every one is either closed in Lean or reduced to the one named fact where every possible machine stops.

## Check it yourself

```
lake exe cache get
lake build
```

The build prints the axioms the theorem rests on: `propext, Classical.choice, Quot.sound`, Lean's standard three.
No `sorry`, no extra assumptions.

## Files

- `Mistranslation.lean`: the headline theorem.
- `Mistranslation/MemsOde.lean`: from the equation to the exact break formula and its existence.
- `Mistranslation/Breaks.lean`: why that break number can't be algebraic.
- `Mistranslation/LindemannBridge.lean`: Hermite-Lindemann (real form) from Lindemann-Weierstrass.
- `Mistranslation/Vendor/Lindemann/`: the Lindemann-Weierstrass theorem, formalized by Yuyang Zhao
  (github.com/astrainfinita/mathlib4, branch `transcendental`), Apache 2.0, copied with credit. Only import paths changed.

## How we got here

1. Downloaded about 1.3 million equations from arXiv papers (2007 to 2023).
2. Wrote a parser that reduces each equation to its shape: how many terms, minus signs and variables, the highest
   derivative, and whether it has a constant.
3. Stored every equation and its shape in a SQL database.
4. Laid the shapes out as a table, a kind of periodic table of equations, where shapes one small change apart sit
   next to each other. Some seats are full and some have never been written.
5. Read the table for patterns. Rows of related equations line up, and walking along one row (forces like
   μ/(1-x)^k) showed that each seat has a "break number" and that the kind of number follows a rule.
6. Solved those seats exactly and checked every step in Lean. This repo is the first of those proofs.

The parser was only the scout. It pointed at which equations to look at, and it misreads plenty. Nothing in these
proofs depends on it: every equation here is written out and solved directly, and Lean checks every step.

I used AI tools a lot for code and writing. The table and the law came from me, and every result is checked by Lean,
so nobody has to take my word or the AI's.

## Context

This is the first piece of a larger result: one rule (the "law of mistranslation") classifies the break numbers of a
whole family of nonlinear boundary value problems as algebraic or transcendental. Questions and corrections welcome.


## The Open Question

Everything this work could prove, it has proved. Every number the law touches has been found, given its formula and sorted, and each one is either closed in Lean or traced to the one place where every machine must stop. That place does not move. More digits will not move it, more computing will not move it, and better instruments will not move it. However fine the instruments become, there is always one more crumb to chase.

So one question is left open, and it is not a question of mathematics:

**Can an instrument ever be perfect? If it can, how would we prove it, what would we use it for, and why? If it cannot, must we wait for perfection before we use it? Or when is good enough, good enough?**

No machine can answer that. A proof can tell us what is true. It cannot tell us what is worth doing, what anything means, or whether a life was spent well. Those things cannot be known from inside the machine, and not before the end. They are answered only by choosing, and only a person can choose. The machine can point the way, but it cannot decide when a transcendent truth is true. It answers only what it is asked. Asking the right question, and deciding when the answer is enough, is ours to do.

**We answer it not once, but every time we choose.**

And we cannot lie to ourselves, because the one who lies is also the one who knows. So choose the way you would choose in the same circumstances, at any time and in any place. If you believe there is no choice, I cannot answer that for you. I can only ask you the same question: do you believe what you say? Until we are honest with each other, and with ourselves, truth cannot exist between us.

That is the frame for every decision, in mathematics and everywhere else: family, friends, work, rest, honesty, trust, even vanity. Each one is weighed in the same light, without trading away the truth, including the truth about ourselves.

Nothing else in the work is left open.

*Quoted from my statement of 23 October 2026.*

Erich Curtis, October 2026. Apache License 2.0.
