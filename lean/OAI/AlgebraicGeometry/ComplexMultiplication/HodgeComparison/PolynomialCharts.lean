import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialEvaluation
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential

/-! # Polynomial Charts -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PolynomialCharts.CM.Construction

noncomputable section

/-! Ordinary polynomial coordinates are members of the genuine regular atlas. -/

open scoped ContDiff _root_.Manifold
open _root_.CategoryTheory _root_.AlgebraicGeometry Set

variable (ι : Type*) [Fintype ι]

def polynomialRegularChart :
    OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial ι ℂ)) (Fin (Fintype.card ι) → ℂ) :=
  ((ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph ι).trans
    (Homeomorph.piCongrLeft (Y := fun _ : Fin (Fintype.card ι) => ℂ) (Fintype.equivFin ι))).toOpenPartialHomeomorph

theorem polynomialRegularChart_apply (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial ι ℂ))
    (k : Fin (Fintype.card ι)) :
    polynomialRegularChart ι x k = x (MvPolynomial.X ((Fintype.equivFin ι).symm k)) := by
  simp [polynomialRegularChart, Homeomorph.piCongrLeft_apply]

theorem polynomialRegularChart_symm_apply (z : Fin (Fintype.card ι) → ℂ) (p : MvPolynomial ι ℂ) :
    (polynomialRegularChart ι).symm z p = MvPolynomial.eval (fun i => z (Fintype.equivFin ι i)) p := rfl

theorem polynomialRegularChart_source : (polynomialRegularChart ι).source = Set.univ := rfl

theorem polynomialRegularChart_target : (polynomialRegularChart ι).target = Set.univ := rfl

theorem polynomialRegularChart_mem_atlas :
    polynomialRegularChart ι ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas (MvPolynomial ι ℂ) (Fintype.card ι) := by
  constructor
  · intro p
    change ContDiffOn ℂ ω (fun z : Fin (Fintype.card ι) → ℂ =>
      MvPolynomial.eval (fun i => z (Fintype.equivFin ι i)) p) Set.univ
    apply ContDiff.contDiffOn
    apply (ComplexPoints.Analytic.PolynomialImplicit.contDiff_polynomial_eval p ω).comp
    apply contDiff_pi.mpr
    intro i
    exact (ContinuousLinearMap.proj (Fintype.equivFin ι i) :
      (Fin (Fintype.card ι) → ℂ) →L[ℂ] ℂ).contDiff
  · refine ⟨1, ?_, ?_⟩
    · intro x _
      simp
    · intro k
      refine ⟨MvPolynomial.X ((Fintype.equivFin ι).symm k), 0, ?_⟩
      intro x _
      simp only [polynomialRegularChart_apply, pow_zero, div_one]

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]

local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)

/-- Every regular chart on an actual affine open is holomorphic for the native atlas. -/
theorem native_affineChart_smooth (A : CommAlgCat ℂ) (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
    [IsOpenImmersion i.left] {n : ℕ}
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) :
    ContMDiffOn 𝓘(ℂ, ModelX) 𝓘(ℂ, Fin n → ℂ) ω (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A i e)
      (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A i e).source := by
  apply contMDiffOn_iff.mpr
  refine ⟨(ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A i e).continuousOn, ?_⟩
  intro x y
  have hc : chartAt ModelX x ∈ ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.schemeRegularAtlas X
      (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) := chart_mem_atlas ModelX x
  obtain ⟨U, hU, c, hc, hchart⟩ := hc
  have hd := ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contDiffOn_affineMap_regularCharts
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) A
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) i c e hc he
  have ht : (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) c).target = c.target := rfl
  simpa only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source,
    extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ, Function.comp_def, id_eq, Set.preimage,
    Set.mem_ofPred_eq, Set.ofPred_mem_eq, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, OpenPartialHomeomorph.refl_source,
    Set.preimage_univ, hchart, ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_symm_apply, ht,
    Set.mem_univ, Set.ofPred_true] using hd

/-- The inverse of a regular affine chart is also holomorphic in the native atlas. -/
theorem native_affineChart_symm_smooth (A : CommAlgCat ℂ) (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
    [IsOpenImmersion i.left] {n : ℕ}
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) :
    ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ModelX) ω (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A i e).symm
      (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A i e).target := by
  apply contMDiffOn_iff.mpr
  refine ⟨(ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A i e).symm.continuousOn, ?_⟩
  intro x y
  have hd := ComplexPoints.Analytic.AffineOpenDifferential.contDiffOn_affinePointMap_regularCharts A i e (chartAt ModelX y)
    he (chart_mem_atlas ModelX y)
  have ht : (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A i e).target = e.target := rfl
  simpa only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source,
    extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ, Function.comp_def, id_eq, Set.preimage,
    Set.mem_ofPred_eq, Set.ofPred_mem_eq, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, OpenPartialHomeomorph.refl_target,
    OpenPartialHomeomorph.refl_symm, Set.univ_inter, ht,
    ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_symm_apply] using hd

theorem native_affineChart_mdifferentiable (A : CommAlgCat ℂ) (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
    [IsOpenImmersion i.left] {n : ℕ}
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) :
    (ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A i e).MDifferentiable 𝓘(ℂ, ModelX) 𝓘(ℂ, Fin n → ℂ) :=
  ⟨(native_affineChart_smooth A i e he).mdifferentiableOn (by simp),
    (native_affineChart_symm_smooth A i e he).mdifferentiableOn (by simp)⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PolynomialCharts.CM.Construction
