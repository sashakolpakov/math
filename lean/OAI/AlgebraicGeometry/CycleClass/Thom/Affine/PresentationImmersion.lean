import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialRegularChart
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothClosedImmersion
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeAffineTopology

/-! # Presentation Immersion -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PresentationImmersion.Constructions

noncomputable section

/-! Actual polynomial presentation coordinates give a closed holomorphic immersion of a smooth affine point manifold. -/

open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialRegularChart.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type} [CommRing A] [Algebra ℂ A] [IsDomain A] [Algebra.Smooth ℂ A]
  {n : ℕ} (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A)

def presentationCoordinates (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (j : Fin n) : ℂ := x (f (MvPolynomial.X j))

theorem presentationCoordinates_analytic (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ) 𝓘(ℂ, Fin n → ℂ) r
      (presentationCoordinates f) :=
  contMDiff_pi_space.mpr (fun j => ComplexPoints.Analytic.SmoothAffineMaps.contMDiff_smoothDomain_eval (f (MvPolynomial.X j)) r)

theorem presentationCoordinates_mfderiv (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    mfderiv 𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ) 𝓘(ℂ, Fin n → ℂ)
      (presentationCoordinates f) x =
    fderiv ℂ (fun z => presentationCoordinates f
      ((chartAt (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ) x).symm z))
      (chartAt (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ) x x) := by
  rw [((presentationCoordinates_analytic f 1).mdifferentiableAt (x := x) one_ne_zero).mfderiv_abuse]
  simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, Function.comp_def, id_eq, Set.range_id, fderivWithin_univ]

theorem presentationCoordinates_differential_injective (hf : Function.Surjective f)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    Function.Injective (mfderiv 𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ)
      𝓘(ℂ, Fin n → ℂ) (presentationCoordinates f) x) := by
  rw [presentationCoordinates_mfderiv]
  exact ComplexPoints.Analytic.SmoothClosedImmersion.fderiv_affineChartComap_injective_of_surjective f hf
    (chartAt (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ) x)
    (ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph (Fin n)).toOpenPartialHomeomorph
    (chart_mem_atlas _ x) (PolynomialRegularChart.Constructions.polynomial_chart_regular n) x (mem_chart_source _ x) (by trivial)

omit [IsDomain A] [Algebra.Smooth ℂ A] in
theorem presentationCoordinates_closedEmbedding (hf : Function.Surjective f) :
    Topology.IsClosedEmbedding (presentationCoordinates f) := ComplexPoints.Analytic.FiniteTypeAffineTopology.isClosedEmbedding_polynomialPresentation f hf

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PresentationImmersion.Constructions
