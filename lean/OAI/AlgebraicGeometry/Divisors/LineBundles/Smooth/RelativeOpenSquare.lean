import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Relative Open Square -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.RelativeOpenSquare.BundleCycles

noncomputable section

/-! Smooth relative dimension is retained by an actual open source chart
over an open target, whether or not that chart exhausts the inverse image. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

theorem smoothRelativeDimension_openSquare {E X V U : Scheme.{0}}
    (p : E ⟶ X) (n : ℕ) [SmoothOfRelativeDimension n p] (q : V ⟶ U)
    (i : U ⟶ X) (j : V ⟶ E) [IsOpenImmersion i] [IsOpenImmersion j]
    (h : q ≫ i = j ≫ p) : SmoothOfRelativeDimension n q := by
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  let k : V ⟶ pullback p i := pullback.lift j q h.symm
  have hk : k ≫ pullback.fst p i = j := pullback.lift_fst _ _ _
  have hq : k ≫ pullback.snd p i = q := pullback.lift_snd _ _ _
  let : IsOpenImmersion (k ≫ pullback.fst p i) := hk.symm ▸ inferInstance
  let : IsOpenImmersion k := IsOpenImmersion.of_comp k (pullback.fst p i)
  let : SmoothOfRelativeDimension n (pullback.snd p i) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback p i) inferInstance
  have H := smoothOfRelativeDimension_comp 0 n k (pullback.snd p i)
  rwa [zero_add, hq] at H

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.RelativeOpenSquare.BundleCycles
