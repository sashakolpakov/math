import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.TensorPointHomeomorph
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.EvaluationAnalytic
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.Immersion

/-! # Graph Ambient Analytic -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphAmbientAnalytic.Constructions

noncomputable section

/-! The genuine tensor-product affine ambient space and the analytic product ambient space are holomorphically homeomorphic. -/

open scoped _root_.Manifold ContDiff TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.TensorPointHomeomorph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.EvaluationAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PresentationImmersion.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type) [CommRing R] [Algebra ℂ R] [IsDomain R] [Algebra.Smooth ℂ R] (n : ℕ)
  [IsDomain (R ⊗[ℂ] MvPolynomial (Fin n) ℂ)]
  [Algebra.Smooth ℂ (R ⊗[ℂ] MvPolynomial (Fin n) ℂ)]

local notation "ModelR" => Fin (OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ R) → ℂ
local notation "ModelT" => Fin (OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ (R ⊗[ℂ] MvPolynomial (Fin n) ℂ)) → ℂ

local instance (priority := low) : ChartedSpace (ModelR × (Fin n → ℂ))
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints R × (Fin n → ℂ)) :=
  prodChartedSpace ModelR (Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) (Fin n → ℂ) (Fin n → ℂ)
local instance : IsManifold 𝓘(ℂ, ModelR × (Fin n → ℂ)) ω
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints R × (Fin n → ℂ)) := Product.Immersion.Constructions.productModel_isManifold

theorem affineGraphHomeomorph_analytic :
    ContMDiff 𝓘(ℂ, ModelT) 𝓘(ℂ, ModelR × (Fin n → ℂ)) ω (TensorPointHomeomorph.Constructions.affineGraphHomeomorph R n) := by
  change ContMDiff _ _ ω (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (R ⊗[ℂ] MvPolynomial (Fin n) ℂ) =>
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap Algebra.TensorProduct.includeLeft x,
      PresentationImmersion.Constructions.presentationCoordinates Algebra.TensorProduct.includeRight x))
  rw [modelWithCornersSelf_prod]
  exact (ComplexPoints.Analytic.SmoothAffineMaps.contMDiff_smoothDomain_comap
    (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] MvPolynomial (Fin n) ℂ) ω).prodMk
    (PresentationImmersion.Constructions.presentationCoordinates_analytic
      (Algebra.TensorProduct.includeRight : MvPolynomial (Fin n) ℂ →ₐ[ℂ]
        R ⊗[ℂ] MvPolynomial (Fin n) ℂ) ω)

theorem affineGraphHomeomorph_symm_analytic :
    ContMDiff 𝓘(ℂ, ModelR × (Fin n → ℂ)) 𝓘(ℂ, ModelT) ω (TensorPointHomeomorph.Constructions.affineGraphHomeomorph R n).symm := by
  apply EvaluationAnalytic.Constructions.contMDiff_affine_of_eval _ (TensorPointHomeomorph.Constructions.affineGraphHomeomorph R n).symm.continuous
  intro t
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add]; exact ha.add hb
  | tmul a b =>
    change ContMDiff _ _ ω (fun z : Foundations.Scheme.AffineComplexPoints.affineComplexPoints R × (Fin n → ℂ) =>
      z.1 a * MvPolynomial.eval z.2 b)
    rw [modelWithCornersSelf_prod]
    exact ((ComplexPoints.Analytic.SmoothAffineMaps.contMDiff_smoothDomain_eval a ω).comp contMDiff_fst).mul
      ((ComplexPoints.Analytic.PolynomialImplicit.contDiff_polynomial_eval b ω).contMDiff.comp contMDiff_snd)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphAmbientAnalytic.Constructions
