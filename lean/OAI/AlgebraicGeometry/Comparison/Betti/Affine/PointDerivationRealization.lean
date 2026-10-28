import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartCotangentRealization

/-! # Point Derivation Realization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.PointDerivationRealization

noncomputable section

/-! Every algebraic derivation at a smooth affine complex point is an actual chart tangent vector. -/

open scoped TensorProduct

variable {A : Type} [CommRing A] [Algebra ℂ A] [IsDomain A] [Algebra.Smooth ℂ A]

theorem affinePointDerivation_exists_chartVector
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)
      (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A))
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source) :
    let _ : Algebra A ℂ := x.toRingHom.toAlgebra
    ∀ D : Derivation ℂ A ℂ, ∃ v : Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ,
      ∀ a, ChartCotangentRealization.affineChartRegularDifferential e x a v = D a := by
  let : Algebra A ℂ := x.toRingHom.toAlgebra
  let : IsScalarTower ℂ A ℂ := IsScalarTower.of_algebraMap_eq' x.comp_algebraMap.symm
  dsimp only
  intro D
  let E := LinearEquiv.ofBijective (ChartCotangentRealization.affineChartCotangentRealization e he x hx)
    (ChartCotangentRealization.affineChartCotangentRealization_bijective e he x hx)
  let L := D.liftKaehlerDifferential.liftBaseChange ℂ
  let φ := L.comp E.symm.toLinearMap
  refine ⟨(Module.evalEquiv ℂ (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ)).symm φ, ?_⟩
  intro a
  rw [Module.apply_evalEquiv_symm_apply]
  change L (E.symm (ChartCotangentRealization.affineChartRegularDifferential e x a)) = D a
  have hE : E (1 ⊗ₜ[A] KaehlerDifferential.D ℂ A a) =
      ChartCotangentRealization.affineChartRegularDifferential e x a := ChartCotangentRealization.affineChartCotangentRealization_D e he x hx a
  rw [← hE, E.symm_apply_apply]
  change (D.liftKaehlerDifferential.liftBaseChange ℂ) (1 ⊗ₜ[A] KaehlerDifferential.D ℂ A a) = D a
  rw [LinearMap.liftBaseChange_one_tmul, Derivation.liftKaehlerDifferential_comp_D]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.PointDerivationRealization
