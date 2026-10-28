import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PrincipalCoefficientPresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrincipalOpenImmersionDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoefficientImmersionFlattening

/-! # Affine Open Immersion Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.AffineOpenImmersionDescent

noncomputable section

/-! Open immersions between flat finite type affine models descend to finite coefficients. -/

open TensorProduct _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_flat_affine_openImmersion_descent
    {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
    [Algebra C R] [Algebra C A] [Algebra C B]
    [Algebra.FiniteType C A] [Algebra.FiniteType C B]
    [Module.Flat C A] [Module.Flat C B] (φ : A →ₐ[C] B)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id R R) φ).toRingHom))]
    (E : Subalgebra C R) (hE : E.FG) :
    ∃ F : Subalgebra C R, E ≤ F ∧ F.FG ∧
      IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id F F) φ).toRingHom)) := by
  obtain ⟨D, hED, hD, k, f, hcover, hiso⟩ :=
    Affine.PrincipalCoefficientPresentation.exists_affine_principal_coefficient_presentation φ E hE
  let φD := Algebra.TensorProduct.map (AlgHom.id D D) φ
  obtain ⟨F, _, hF, _, _, hopen⟩ := PrincipalOpenImmersionDescent.exists_principal_openImmersion_descent
    φD f hcover hiso (⊥ : Subalgebra D R) Subalgebra.fg_bot
  have := hopen
  obtain ⟨hDF, hfg, hImm⟩ := Finite.CoefficientImmersionFlattening.finite_coefficient_immersion_flatten D F hD hF φ
  exact ⟨F.restrictScalars C, hED.trans hDF, hfg, hImm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.AffineOpenImmersionDescent
