import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Basic.Complex.Basic

/-! # Generic Smooth Neighborhood -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.GenericSmoothNeighborhood.Abelian

noncomputable section

/-!
A complex point whose arithmetic image is generic in an integral rational
scheme factors through a smooth open neighborhood. This uses perfection of
the rational field and the actual generic smooth locus.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem generic_complex_point_factors_through_smooth_open
    {X : Scheme} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of ℚ)) [LocallyOfFinitePresentation f]
    (p : Spec (CommRingCat.of ℂ) ⟶ X)
    (hp : p (IsLocalRing.closedPoint ℂ) = genericPoint X) :
    ∃ U : X.Opens, IsIntegral U ∧ Smooth (U.ι ≫ f) ∧
      ∃ q : Spec (CommRingCat.of ℂ) ⟶ U, q ≫ U.ι = p := by
  let U := f.smoothLocus
  have hU : genericPoint X ∈ U := f.genericPoint_mem_smoothLocus_of_perfectField
  let : Nonempty U := ⟨⟨genericPoint X, hU⟩⟩
  have hInt : IsIntegral U := isIntegral_of_isOpenImmersion U.ι
  have hSmooth : Smooth (U.ι ≫ f) := by
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    apply le_antisymm le_top
    intro x _
    exact x.property
  have hrange : Set.range p ⊆ Set.range U.ι := by
    rintro z ⟨w, rfl⟩
    have hw : w = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    rw [hw, hp]
    exact ⟨⟨genericPoint X, hU⟩, rfl⟩
  exact ⟨U, hInt, hSmooth, IsOpenImmersion.lift U.ι p hrange, IsOpenImmersion.lift_fac _ _ _⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.GenericSmoothNeighborhood.Abelian
