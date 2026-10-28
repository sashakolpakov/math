/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This file has been modified.
-/
module

public import ComparatorChallenges.HodgeConjectureCMAbelianVarieties.CM

/-!
# Comparator challenge: the Hodge conjecture for CM abelian varieties

The conclusion is the literal conclusion of the upstream abelian-variety
special case. The only added condition is complex multiplication on H¹.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ComplexPoint

namespace HodgeCM

set_option warningAsError false in
/-- Every rational Hodge class on a complex CM abelian variety is a rational
linear combination of classes of algebraic subvarieties. -/
theorem hodge_conjecture_for_cm_abelian_varieties
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [GrpObj X]
    (hCM : HasComplexMultiplication X) (p : ℕ) :
    Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  sorry

end HodgeCM
