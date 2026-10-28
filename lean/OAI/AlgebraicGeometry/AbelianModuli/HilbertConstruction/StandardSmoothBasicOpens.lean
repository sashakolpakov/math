import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Standard Smooth Basic Opens -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StandardSmoothBasicOpens

noncomputable section

/-! Restricting a standard smooth affine chart to a basic open of its base preserves its relative dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem standardSmooth_basicOpen_appLE {X S : Scheme.{u}} (p : X ⟶ S)
    {U : S.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (e : V ≤ p ⁻¹ᵁ U) (d : ℕ)
    (h : RingHom.IsStandardSmoothOfRelativeDimension d (p.appLE U V e).hom) (r : Γ(S, U)) :
    RingHom.IsStandardSmoothOfRelativeDimension d
      (p.appLE (S.basicOpen r) (X.basicOpen (p.appLE U V e r))
        (by simp [Scheme.Hom.appLE])).hom := by
  have := hU.isLocalization_basicOpen r
  have := hV.isLocalization_basicOpen (p.appLE U V e r)
  rw [hU.appLE_eq_away_map p hV]
  exact (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves d).away _ _ _ _ h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StandardSmoothBasicOpens
