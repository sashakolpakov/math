import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphAmbientAnalytic
import OAI.AlgebraicGeometry.CycleClass.Thom.SmoothAffineGlobalCoordinates
import OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductDomain

/-! # Affine Graph Ambient -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.AffineGraphAmbient.Constructions

/-! Smoothness, integrality, and dimension of the actual polynomial graph ambient scheme follow from the base algebra. -/

open scoped TensorProduct _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphAmbientAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.TensorPointHomeomorph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorph.Constructions

variable (R : Type) [CommRing R] [Algebra ℂ R] [IsDomain R] [Algebra.Smooth ℂ R] (n : ℕ)

instance instIsDomainGraphAmbient_proofs : IsDomain (R ⊗[ℂ] MvPolynomial (Fin n) ℂ) :=
  Tensor.ProductDomain.Constructions.tensorProduct_isDomain

instance instSmoothGraphAmbient_proofs : Algebra.Smooth ℂ (R ⊗[ℂ] MvPolynomial (Fin n) ℂ) := by
  let : Algebra.Smooth ℂ (MvPolynomial (Fin n) ℂ) := {}
  exact Algebra.Smooth.comp ℂ R (R ⊗[ℂ] MvPolynomial (Fin n) ℂ)

theorem graphAmbient_rank (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) :
    Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ (R ⊗[ℂ] MvPolynomial (Fin n) ℂ) =
      Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ R + n := by
  let : ChartedSpace ((Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ R) → ℂ) × (Fin n → ℂ))
      (Foundations.Scheme.AffineComplexPoints.affineComplexPoints R × (Fin n → ℂ)) :=
    prodChartedSpace (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ R) → ℂ)
      (Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) (Fin n → ℂ) (Fin n → ℂ)
  have h := HolomorphicHomeomorph.Constructions.homeomorph_model_finrank (Affine.TensorPointHomeomorph.Constructions.affineGraphHomeomorph R n)
    ((Affine.GraphAmbientAnalytic.Constructions.affineGraphHomeomorph_analytic R n).mdifferentiable (by simp))
    ((Affine.GraphAmbientAnalytic.Constructions.affineGraphHomeomorph_symm_analytic R n).mdifferentiable (by simp))
    ((Affine.TensorPointHomeomorph.Constructions.affineGraphHomeomorph R n).symm (x, 0))
  simpa only [Module.finrank_fin_fun, Module.finrank_prod] using h

end AlgebraicGeometry.CycleClass.Thom.AffineGraphAmbient.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.AffineGraphAmbient.Constructions.Scheme

/-! The actual affine graph scheme has a holomorphic product ambient space with exactly its given base map and polynomial coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.TensorPointHomeomorph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphScheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphRingMap.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PresentationImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphAmbientAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.AffineGraphAmbient.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SmoothAffineGlobalCoordinates.Constructions.Spec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type) [CommRing R] [Algebra ℂ R] (n : ℕ)

def schemeGraphHomeomorph :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (R ⊗[ℂ] MvPolynomial (Fin n) ℂ)) ≃ₜ
      (Foundations.Scheme.AffineComplexPoints.affineComplexPoints R × (Fin n → ℂ)) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointHomeomorph (R ⊗[ℂ] MvPolynomial (Fin n) ℂ)).symm.trans
    (Affine.TensorPointHomeomorph.Constructions.affineGraphHomeomorph R n)

theorem schemeGraphHomeomorph_graph {A : Type} [CommRing A] [Algebra ℂ A]
    (h : R →ₐ[ℂ] A) (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    schemeGraphHomeomorph R n
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Affine.GraphScheme.Constructions.graphSchemeMap h f) (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A x)) =
        (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h x, Affine.PresentationImmersion.Constructions.presentationCoordinates f x) := by
  rw [Affine.GraphScheme.Constructions.graphSchemeMap_point]
  change Affine.TensorPointHomeomorph.Constructions.affineGraphHomeomorph R n
    ((ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointHomeomorph _).symm ((ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointHomeomorph _) (x.comp (Affine.GraphRingMap.Constructions.graphRingMap h f)))) = _
  rw [Homeomorph.symm_apply_apply]
  exact Affine.TensorPointHomeomorph.Constructions.affineGraphHomeomorph_graph h f x

variable [IsDomain R] [Algebra.Smooth ℂ R]

local notation "ModelR" => Fin (OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ R) → ℂ
local notation "ModelT" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension
  (Over.hom (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (R ⊗[ℂ] MvPolynomial (Fin n) ℂ)))) → ℂ

local instance (priority := low) : ChartedSpace (ModelR × (Fin n → ℂ))
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints R × (Fin n → ℂ)) :=
  prodChartedSpace ModelR (Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) (Fin n → ℂ) (Fin n → ℂ)

theorem schemeGraphHomeomorph_analytic :
    ContMDiff 𝓘(ℂ, ModelT) 𝓘(ℂ, ModelR × (Fin n → ℂ)) ω (schemeGraphHomeomorph R n) :=
  (Affine.GraphAmbientAnalytic.Constructions.affineGraphHomeomorph_analytic R n).comp
    (SmoothAffineGlobalCoordinates.Constructions.Spec.affineSchemePointHomeomorph_symm_analytic (R ⊗[ℂ] MvPolynomial (Fin n) ℂ))

theorem schemeGraphHomeomorph_symm_analytic :
    ContMDiff 𝓘(ℂ, ModelR × (Fin n → ℂ)) 𝓘(ℂ, ModelT) ω (schemeGraphHomeomorph R n).symm :=
  (SmoothAffineGlobalCoordinates.Constructions.Spec.affineSchemePointHomeomorph_analytic (R ⊗[ℂ] MvPolynomial (Fin n) ℂ)).comp
    (Affine.GraphAmbientAnalytic.Constructions.affineGraphHomeomorph_symm_analytic R n)

theorem schemeGraphHomeomorph_dimension (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension
      (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (R ⊗[ℂ] MvPolynomial (Fin n) ℂ)).hom =
      Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ R + n :=
  (SmoothAffineGlobalCoordinates.Constructions.Spec.affineScheme_modelDimension (R ⊗[ℂ] MvPolynomial (Fin n) ℂ)
    ((Affine.TensorPointHomeomorph.Constructions.affineGraphHomeomorph R n).symm (x, 0))).symm.trans (graphAmbient_rank R n x)

end AlgebraicGeometry.CycleClass.Thom.AffineGraphAmbient.Constructions.Scheme

end

end OAI
