import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.EtaleDifferential
import OAI.AlgebraicGeometry.CycleClass.Thom.EtaleCoordinateDimension

/-! # Etale Coordinate Analytic -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.EtaleCoordinateAnalytic.Constructions

noncomputable section

/-! Genuine unramified polynomial coordinates have injective analytic
differential. With the actual dimension count they are local analytic
coordinates on the native affine scheme manifold. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PresentationImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialRegularChart.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.EtaleDifferential.Constructions.Construction
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SmoothAffineGlobalCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorph.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem presentationCoordinates_unramified_injective
    {A : Type} [CommRing A] [Algebra ℂ A] [IsDomain A] [Algebra.Smooth ℂ A]
    {n : ℕ} (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (hf : f.toRingHom.FormallyUnramified)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    Function.Injective (mfderiv 𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ)
      𝓘(ℂ, Fin n → ℂ) (Affine.PresentationImmersion.Constructions.presentationCoordinates f) x) := by
  rw [Affine.PresentationImmersion.Constructions.presentationCoordinates_mfderiv]
  exact ProperImage.EtaleDifferential.Constructions.Construction.fderiv_affineChartComap_injective_of_unramified f hf
    (chartAt (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ) x)
    (ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph (Fin n)).toOpenPartialHomeomorph
    (chart_mem_atlas _ x) (PolynomialRegularChart.Constructions.polynomial_chart_regular n) x (mem_chart_source _ x) (by trivial)

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] [IsIntegral X.left] [Smooth X.hom]
  (n : ℕ) (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(X.left, ⊤))
  (hf : f.toRingHom.FormallyUnramified)

local notation "MX" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

include hf in
theorem globalCoordinates_unramified_injective (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    Function.Injective (mfderiv 𝓘(ℂ, MX) 𝓘(ℂ, Fin n → ℂ) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) x) := by
  change Function.Injective (mfderiv _ _ (Affine.PresentationImmersion.Constructions.presentationCoordinates f ∘ ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph X) x)
  rw [mfderiv_comp x ((Affine.PresentationImmersion.Constructions.presentationCoordinates_analytic f ω).mdifferentiable (by simp) _)
    ((SmoothAffineGlobalCoordinates.Constructions.affineNativePointHomeomorph_analytic X).mdifferentiable (by simp) x)]
  exact (presentationCoordinates_unramified_injective f hf _).comp
    (HolomorphicHomeomorph.Constructions.homeomorph_mfderiv_bijective (ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph X)
      ((SmoothAffineGlobalCoordinates.Constructions.affineNativePointHomeomorph_analytic X).mdifferentiable (by simp))
      ((SmoothAffineGlobalCoordinates.Constructions.affineNativePointHomeomorph_symm_analytic X).mdifferentiable (by simp)) x).injective

include hf in
theorem globalCoordinates_unramified_bijective (hd : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom = n)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    Function.Bijective (mfderiv 𝓘(ℂ, MX) 𝓘(ℂ, Fin n → ℂ) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) x) := by
  let L : MX →L[ℂ] (Fin n → ℂ) := mfderiv 𝓘(ℂ, MX) 𝓘(ℂ, Fin n → ℂ) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) x
  have hi : Function.Injective L := globalCoordinates_unramified_injective X n f hf x
  change Function.Bijective L
  refine ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := L.toLinearMap) ?_).mp hi⟩
  simpa only [Module.finrank_fin_fun] using hd

end

end OAI.AlgebraicGeometry.CycleClass.Thom.EtaleCoordinateAnalytic.Constructions
