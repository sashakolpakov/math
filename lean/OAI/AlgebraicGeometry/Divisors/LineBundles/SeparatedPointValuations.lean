import OAI.AlgebraicGeometry.Divisors.LineBundles.DVRAbsoluteValue
import OAI.AlgebraicGeometry.Divisors.LineBundles.SeparatedStalkImages

/-! # Separated Point Valuations -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SeparatedPointValuations.BundleCycles

noncomputable section

/-! Distinct DVR points of a separated integral scheme induce
inequivalent absolute values on the actual function field. -/

open _root_.AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [X.IsSeparated]

theorem point_eq_of_stalkAbsoluteValues_equiv (x y : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk y)]
    (h : (DVRAbsoluteValue.BundleCycles.dvrAbsoluteValue (X.presheaf.stalk x) X.functionField).IsEquiv
      (DVRAbsoluteValue.BundleCycles.dvrAbsoluteValue (X.presheaf.stalk y) X.functionField)) : x = y := by
  apply SeparatedStalkImages.BundleCycles.point_eq_of_stalkImages_eq x y
  ext g
  change (∃ a : X.presheaf.stalk x, algebraMap _ X.functionField a = g) ↔
    (∃ a : X.presheaf.stalk y, algebraMap _ X.functionField a = g)
  rw [← DVRAbsoluteValue.BundleCycles.dvrAbsoluteValue_le_one_iff, ← DVRAbsoluteValue.BundleCycles.dvrAbsoluteValue_le_one_iff]
  exact h.le_one_iff

theorem stalkAbsoluteValues_pairwise_inequivalent {ι : Type*} (x : ι → X)
    [∀ i, IsDiscreteValuationRing (X.presheaf.stalk (x i))] (hx : Function.Injective x) :
    Pairwise fun i j => ¬ (DVRAbsoluteValue.BundleCycles.dvrAbsoluteValue (X.presheaf.stalk (x i)) X.functionField).IsEquiv
      (DVRAbsoluteValue.BundleCycles.dvrAbsoluteValue (X.presheaf.stalk (x j)) X.functionField) := by
  intro i j hij h
  exact hij (hx (point_eq_of_stalkAbsoluteValues_equiv (x i) (x j) h))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SeparatedPointValuations.BundleCycles
