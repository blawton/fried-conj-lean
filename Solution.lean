/-
Solution.lean — the development, re-exported for `leanprover/comparator`.

`comparator` compares the constants named in `comparator.json` between this module's environment
and `Challenge.lean`'s. Nothing is proved here: the compared theorem
`FriedCrossing.fried_counterexample_of_resolvent_inputs` is proved in
`B1s/fried_counterexample_main.lean`, whose import chain is the crossing leg
(`fried_crossing_9_03` → `_rate_9_07` → `_firstvariation_9_08` → `_purezeros_9_08` →
`fried_cluster_matrices_9_10` → `resolvent_scale_9_11` + `cluster_from_resolvent_9_11`).
The development never imports `Challenge`.
-/
import B1s.fried_counterexample_main
