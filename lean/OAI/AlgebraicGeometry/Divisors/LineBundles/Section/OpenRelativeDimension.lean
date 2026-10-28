import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.OpenRestriction

/-! # Open Relative Dimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Section.OpenRelativeDimension.BundleCycles

noncomputable section

/-! Restricting the actual projection of a section preserves its smooth
relative dimension on compatible source and target opens. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem smoothRelativeDimension_morphismRestrict {X Y : Scheme.{0}}
    (p : Y ⟶ X) (n : ℕ) [SmoothOfRelativeDimension n p] (V : X.Opens) :
    SmoothOfRelativeDimension n (p ∣_ V) := by
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  exact MorphismProperty.of_isPullback (isPullback_morphismRestrict p V).flip inferInstance

theorem sectionOpenProjection_relativeDimension {X Y : Scheme.{0}}
    (p : Y ⟶ X) (n : ℕ) [SmoothOfRelativeDimension n p]
    (U : Y.Opens) (V : X.Opens) (hU : U ≤ p ⁻¹ᵁ V) :
    SmoothOfRelativeDimension n (OpenRestriction.BundleCycles.sectionOpenProjection p U V hU) := by
  let : SmoothOfRelativeDimension n (p ∣_ V) := smoothRelativeDimension_morphismRestrict p n V
  have H : SmoothOfRelativeDimension (0 + n) (Y.homOfLE hU ≫ p ∣_ V) :=
    smoothOfRelativeDimension_comp 0 n (Y.homOfLE hU) (p ∣_ V)
  change SmoothOfRelativeDimension n (Y.homOfLE hU ≫ p ∣_ V)
  simpa only [zero_add] using H

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Section.OpenRelativeDimension.BundleCycles
