# clocked-chip-firing
A 34-vertex counterexample to Jiang’s subcycle conjecture for parallel chip-firing. A 35-chip configuration has least period 18 on a graph whose only simple cycle lengths are 6 and 27.

# An 18-tick counterexample to Jiang’s subcycle conjecture

In parallel chip-firing, every vertex holding at least its degree in chips sends one chip to each neighbor. All vertices decide whether to fire from the same configuration. Jiang proposed that the eventual period must divide the length of one subcycle or equal the least common multiple (LCM) of the lengths of some disjoint subcycles.

**Theorem.** A connected simple graph on 34 vertices admits a 35-chip configuration of least period 18. Its only ordinary simple cycle lengths are 6 and 27.

[Read the theorem and its 18-tick proof](Clocked_Chip_Firing_Theorem.pdf).

## Construct the example

Join a 6-cycle and a 27-cycle to a new hub by one edge from the hub to vertex 0 of each ring. Give the hub zero chips. Read the following counts in cyclic order starting at vertex 0, then add one chip at vertex 0 of each ring.

| Ring | Base chip counts | Copies around the ring |
| --- | --- | --- |
| 6-cycle | `2 0 2 0 1 1` | 1 |
| 27-cycle | `2 0 2 0 1 1 2 0 1` | 3 |

## Why the first return is tick 18

On an isolated ring, one tick shifts each base pattern by one position. The proof tracks three extra counts at the two bridge entrances and the hub. Its 18-row table shows that each entrance fires on the same ticks as in the isolated rotation, and that all three extra counts return to their starting values at tick 18.

A fixed vertex away from each entrance therefore sees a sequence of least period 6 on the left and 9 on the right. Every return time must be a multiple of both. Their LCM is 18, which proves the displayed return is the first.

Both hub edges are bridges, so every simple cycle lies entirely within one ring. The period 18 divides neither 6 nor 27, and the LCM of the two lengths is 54. Allowing two-step edge backtracks adds 2 as a possible length and still cannot produce an LCM of 18. The distinction between equality and divisibility matters here because 18 *does* divide 54.

## Lean formalization

The paper identifies the declarations `ClockedChipFiring.exact_period_eighteen`, `ClockedChipFiring.simple_cycle_lengths`, and `ClockedChipFiring.not_jiang_cycle_conjecture`. With the companion source in a Lean 4.20.0 project using mathlib v4.20.0, check it from the project directory with:

```sh
lake env lean ClockedChipFiring.lean
```

## License

The original Lean formalization and accompanying documentation are licensed under the [Apache License, Version 2.0](LICENSE).
