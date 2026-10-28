import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceEnlargement
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.FiniteAffineOpens

/-! # Source Finite Affine Opens -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceFiniteAffineOpens

noncomputable section

/-! Finitely many affine opens of a fixed arithmetic scheme's field
base change spread as actual affine opens on a coefficient base change
of that same arithmetic scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Coefficients
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

theorem fixed_source_finite_affine_opens {I : Type} [Finite I]
    (X : Over (Spec (.of R))) (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    (U : I → ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X).left.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) :
    ∃ (s : Finset K) (V : I → ((Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).obj X).left.Opens),
      (∀ i, IsAffineOpen (V i)) ∧
      (∀ i, (CoefficientModels.Coefficients.fixedSourceModel R K s X hX).specialization ⁻¹ᵁ V i = U i) := by
  let M := CoefficientModels.Coefficients.fixedSourceModel R K ∅ X hX
  obtain ⟨s, hs, V, hV, hpre⟩ := Coefficient.FiniteAffineOpens.Coefficients.finite_affine_opens_in_fixed_model
    (Coefficient.Finiteness.Coefficients.baseChange_finitePresentation _ _ hX) M U hU
  change (∅ : Finset K) ⊆ s at hs
  let e := SourceEnlargement.Coefficients.fixedSourceEnlargementIso hs X
  have : IsIso e.inv.left := ((Over.forget (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K s)).mapIso e).isIso_inv
  have hp : (CoefficientModels.Coefficients.fixedSourceModel R K s X hX).specialization ≫ e.inv.left =
      Coefficient.Morphisms.Coefficients.genericModelLift M.model M.specialization M.cartesian.w hs := by
    rw [← SourceEnlargement.Coefficients.fixedSourceEnlargement_generic hs X hX, Category.assoc,
      Over.hom_left_inv_left]
    exact Category.comp_id (Coefficient.Morphisms.Coefficients.genericModelLift M.model M.specialization M.cartesian.w hs)
  refine ⟨s, fun i => e.inv.left ⁻¹ᵁ V i, fun i => (hV i).preimage_of_isIso e.inv.left, ?_⟩
  intro i
  rw [← Scheme.Hom.comp_preimage, hp]
  exact hpre i

end Coefficients

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceFiniteAffineOpens
