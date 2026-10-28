import OAI.AlgebraicGeometry.Comparison.Betti.RegularFunctions
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps

/-! # Regular Smoothness -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.RegularSmoothness

noncomputable section

section

/-! Analytic regular-function evaluation in the established native manifold
atlas. The algebraic hypotheses are used to obtain that atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ChartedSpace
open scoped ContDiff _root_.Manifold

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

theorem regularAnalytic_in_schemeChart
    (g : C(ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X, ℂ)) (hg : RegularFunctions.RegularCoordinateAnalytic X g)
    {n : ℕ} (e : OpenPartialHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.schemeRegularAtlas X n) :
    ContDiffOn ℂ ω (fun z => g (e.symm z)) e.target := by
  obtain ⟨U, hU, c, hc, rfl⟩ := he
  exact hg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) n c hc

variable [IsIntegral X.left] [Smooth X.hom]

abbrev NativeModel := Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

/-- The concrete chart-analytic condition gives ordinary complex manifold analyticity. -/
theorem regularAnalytic_contMDiff
    (g : C(ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X, ℂ)) (hg : RegularFunctions.RegularCoordinateAnalytic X g) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, NativeModel X) 𝓘(ℂ, ℂ) r g := by
  apply contMDiff_iff.mpr
  refine ⟨g.continuous, ?_⟩
  intro x y
  have h := regularAnalytic_in_schemeChart X g hg (chartAt (NativeModel X) x)
    (chart_mem_atlas (NativeModel X) x)
  simpa only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source,
    extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ, Function.comp_def, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, OpenPartialHomeomorph.refl_source,
    Set.preimage_univ, id_eq, Set.preimage, Set.mem_ofPred_eq, Set.ofPred_mem_eq,
    Set.mem_univ, Set.ofPred_true] using h.of_le (show r ≤ ω from le_top)

/-- Scalar restriction gives smoothness for the real manifold de Rham complex. -/
theorem regularAnalytic_real_contMDiff
    (g : C(ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X, ℂ)) (hg : RegularFunctions.RegularCoordinateAnalytic X g) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, NativeModel X) 𝓘(ℝ, ℂ) r g := by
  apply contMDiff_iff.mpr
  refine ⟨g.continuous, ?_⟩
  intro x y
  have h := regularAnalytic_in_schemeChart X g hg (chartAt (NativeModel X) x)
    (chart_mem_atlas (NativeModel X) x)
  simpa only [extChartAt_coe, extChartAt_coe_symm, extChartAt_source,
    extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ, Function.comp_def, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, OpenPartialHomeomorph.refl_source,
    Set.preimage_univ, id_eq, Set.preimage, Set.mem_ofPred_eq, Set.ofPred_mem_eq,
    Set.mem_univ, Set.ofPred_true] using
      (h.of_le (show r ≤ ω from le_top)).restrict_scalars ℝ

theorem globalEvaluation_contMDiff (s : Γ(X.left, ⊤)) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, NativeModel X) 𝓘(ℂ, ℂ) r
      (fun p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X => RegularFunctions.globalEvaluation p s) :=
  regularAnalytic_contMDiff X (RegularFunctions.globalSectionContinuousAlgHom X s)
    (RegularFunctions.globalSection_regularAnalytic X s) r

theorem globalEvaluation_real_contMDiff (s : Γ(X.left, ⊤)) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, NativeModel X) 𝓘(ℝ, ℂ) r
      (fun p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X => RegularFunctions.globalEvaluation p s) :=
  regularAnalytic_real_contMDiff X (RegularFunctions.globalSectionContinuousAlgHom X s)
    (RegularFunctions.globalSection_regularAnalytic X s) r

end

/-! Each actual point of a smooth integral complex scheme lies in a
standard smooth affine chart of its native analytic model dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem exists_standardSmooth_scheme_affine_chart (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    ∃ (U : X.left.Opens) (hU : IsAffineOpen U),
      Algebra.IsStandardSmoothOfRelativeDimension (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
        ℂ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) ∧
      ∃ (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U))
        (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) (NativeModel X)),
        e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
          (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) ∧
        x ∈ e.source ∧ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU x = p := by
  let n := Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom
  let : SmoothOfRelativeDimension n X.hom := Betti.SmoothDimension.Realization.smoothOfFunctionFieldDimension X.hom
  obtain ⟨U, hU, V, hV, hpV, eUV, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := n) (f := X.hom) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p)
  have hUtop : U = ⊤ := by
    ext y
    constructor
    · intro _
      trivial
    · intro _
      exact (Subsingleton.elim (X.hom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p)) y) ▸ eUV hpV
  subst U
  let : Algebra.IsStandardSmoothOfRelativeDimension n ℂ
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X V) :=
    Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra_standardSmooth n X.hom V hstd
  have hp : p ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X V hV) := by
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap]
    exact hpV
  obtain ⟨x, hx⟩ := hp
  obtain ⟨e, he, hxe⟩ := ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.exists_standardSmooth_affineRegularChart n x
  exact ⟨V, hV, inferInstance, x, e, he, hxe, hx⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.RegularSmoothness
