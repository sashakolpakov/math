import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ConnectionLogs
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChernSheaf
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.GlobalCurvature
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ConnectionTransgression

/-! # Curvature D -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CurvatureD

noncomputable section

section

/-! The actual metric connection and original transition logarithms in the genuine Čech–de Rham complex. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M] [T2Space M]
  [IsManifold 𝓘(ℂ, E) ∞ M] (u : Connecting.holomorphicUnitCohomology E M)

def holomorphicLineConnectionOnLogIntersection {n : ℕ}
    (a : Fin (n + 1) → Singular.HolomorphicLogIndex E M u) (k : Fin (n + 1)) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (Singular.holomorphicLogCover E M u) a) 1 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict
    ((AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (Singular.holomorphicLogCover E M u) a k).trans (Singular.holomorphicLogCover_subset E M u (a k)))
    (HolomorphicLine.LocalCurvature.holomorphicLineLocalConnectionForm u (a k).2.val)

def holomorphicLineConnectionCech : Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := E) (Singular.holomorphicLogCover E M u) 1 0 :=
  fun a => holomorphicLineConnectionOnLogIntersection u a 0

def holomorphicLineTransitionLogFunction (a : Fin 2 → Singular.HolomorphicLogIndex E M u) :
    Exponential.HolomorphicFunction (E := E) (M := AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (Singular.holomorphicLogCover E M u) a) :=
  ⟨Singular.holomorphicLogCech E M u a, ChernSheaf.holomorphicLogCech_holomorphic E M u a⟩

def holomorphicLineLogarithmFormCech : Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := E) (Singular.holomorphicLogCover E M u) 0 1 :=
  fun a => SmoothScalarForm.smoothScalarOpenZeroForm (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen (holomorphicLineTransitionLogFunction u a))

theorem holomorphicLineConnectionCech_delta_apply (a : Fin 2 → Singular.HolomorphicLogIndex E M u) :
    Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta (Singular.holomorphicLogCover E M u) 1 0 (holomorphicLineConnectionCech u) a =
      holomorphicLineConnectionOnLogIntersection u a 1 - holomorphicLineConnectionOnLogIntersection u a 0 := by
  have hdelta := AlgebraicTopology.DeRham.Comparison.SmoothCech.cechDelta_apply (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf E M 1) (Singular.holomorphicLogCover E M u)
    0 (holomorphicLineConnectionCech u) a
  refine hdelta.trans ?_
  rw [Fin.sum_univ_two]
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  change (1 : ℤ) • HolomorphicLine.LocalCurvature.holomorphicLineLocalConnectionForm u (a 1).2.val
      ⟨x.val, Singular.holomorphicLogCover_subset E M u (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 1 x.property)⟩ v +
    (-1 : ℤ) • HolomorphicLine.LocalCurvature.holomorphicLineLocalConnectionForm u (a 0).2.val
      ⟨x.val, Singular.holomorphicLogCover_subset E M u (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 0 x.property)⟩ v =
    HolomorphicLine.LocalCurvature.holomorphicLineLocalConnectionForm u (a 1).2.val _ v - HolomorphicLine.LocalCurvature.holomorphicLineLocalConnectionForm u (a 0).2.val _ v
  simp only [one_smul, neg_one_smul, sub_eq_add_neg]

theorem holomorphicLineConnectionOnLogIntersection_change (a : Fin 2 → Singular.HolomorphicLogIndex E M u) :
    holomorphicLineConnectionOnLogIntersection u a 0 = holomorphicLineConnectionOnLogIntersection u a 1 +
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (holomorphicLineLogarithmFormCech u a) :=
  ConnectionLogs.holomorphicLineLocalConnectionForm_log_overlap u (a 0).2.val (a 1).2.val
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (Singular.holomorphicLogCover E M u) a)
    (le_inf ((AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 0).trans (Singular.holomorphicLogCover_subset E M u (a 0)))
      ((AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 1).trans (Singular.holomorphicLogCover_subset E M u (a 1))))
    (holomorphicLineTransitionLogFunction u a) (fun x => (Singular.exp_holomorphicLogCech E M u a x).symm)

theorem holomorphicLineConnectionCech_delta :
    Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta (Singular.holomorphicLogCover E M u) 1 0 (holomorphicLineConnectionCech u) =
      -Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechExteriorD (Singular.holomorphicLogCover E M u) 0 1 (holomorphicLineLogarithmFormCech u) := by
  funext a
  rw [holomorphicLineConnectionCech_delta_apply]
  have h := holomorphicLineConnectionOnLogIntersection_change u a
  change holomorphicLineConnectionOnLogIntersection u a 1 - holomorphicLineConnectionOnLogIntersection u a 0 =
    -(Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (holomorphicLineLogarithmFormCech u a))
  rw [h]
  abel

theorem holomorphicLineConnectionCech_d :
    Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechExteriorD (Singular.holomorphicLogCover E M u) 1 0 (holomorphicLineConnectionCech u) =
      Analysis.DifferentialForms.Manifold.CechAugmentation.manifoldCechAugmentation (Singular.holomorphicLogCover E M u) 2 (GlobalCurvature.holomorphicLineGlobalCurvature u) := by
  funext a
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict
    ((AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (Singular.holomorphicLogCover E M u) a 0).trans (Singular.holomorphicLogCover_subset E M u (a 0)))
      (HolomorphicLine.LocalCurvature.holomorphicLineLocalConnectionForm u (a 0).2.val)) = _
  rw [← Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_d]
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict _ (HolomorphicLine.LocalCurvature.holomorphicLineLocalCurvatureForm u (a 0).2.val) = _
  rw [← GlobalCurvature.holomorphicLineGlobalCurvature_onOpen]
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  rfl

theorem holomorphicLine_curvature_logarithmic_boundary :
    (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) (Singular.holomorphicLogCover E M u)).d 1 2
      (ComplexMultiplication.HodgeComparison.ConnectionTransgression.CM.Construction.connectionTotalPrimitive (Singular.holomorphicLogCover E M u)
        (holomorphicLineConnectionCech u) (holomorphicLineLogarithmFormCech u)) =
      (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechAugmentationToTotal (E := E) (Singular.holomorphicLogCover E M u)).f 2 (GlobalCurvature.holomorphicLineGlobalCurvature u) -
        Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion (Singular.holomorphicLogCover E M u) 2 0 2 rfl
          (Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta (Singular.holomorphicLogCover E M u) 0 1 (holomorphicLineLogarithmFormCech u)) :=
  ComplexMultiplication.HodgeComparison.ConnectionTransgression.CM.Construction.connection_curvature_total_boundary (Singular.holomorphicLogCover E M u) (GlobalCurvature.holomorphicLineGlobalCurvature u)
    (holomorphicLineConnectionCech u) (holomorphicLineLogarithmFormCech u)
    (holomorphicLineConnectionCech_d u) (holomorphicLineConnectionCech_delta u)

end

section

/-! The normalized original transition logarithms have exactly the original rational Chern defect. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

def holomorphicCurvatureChernScale : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹

theorem holomorphicCurvatureChernScale_period (z : ℂ) :
    holomorphicCurvatureChernScale * (z * (2 * (Real.pi : ℂ) * Complex.I)) = z := by
  rw [mul_comm z, ← mul_assoc]
  exact (congrArg (fun c : ℂ => c * z) (inv_mul_cancel₀ Complex.two_pi_I_ne_zero)).trans (one_mul z)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M] [T2Space M]
  [IsManifold 𝓘(ℂ, E) ∞ M] (u : Connecting.holomorphicUnitCohomology E M)

def holomorphicLineNormalizedCurvature : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 2 :=
  holomorphicCurvatureChernScale • GlobalCurvature.holomorphicLineGlobalCurvature u

def holomorphicLineNormalizedConnectionCech : Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := E) (Singular.holomorphicLogCover E M u) 1 0 :=
  holomorphicCurvatureChernScale • holomorphicLineConnectionCech u

def holomorphicLineNormalizedLogCech : Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := E) (Singular.holomorphicLogCover E M u) 0 1 :=
  holomorphicCurvatureChernScale • holomorphicLineLogarithmFormCech u

def holomorphicLineRationalDefectForms : Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := E) (Singular.holomorphicLogCover E M u) 0 2 :=
  fun a => Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantManifoldZeroForm E (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (Singular.holomorphicLogCover E M u) a)
    ⟨fun x => ((LogCech.RationalCech.logDefectCech (TopCat.of M) (Singular.holomorphicLogCover E M u)
      (Singular.holomorphicLogCech E M u) (Singular.holomorphicLogCech_cocycle E M u) a x : ℚ) : ℂ),
      (LogCech.RationalCech.logDefectCech (TopCat.of M) (Singular.holomorphicLogCover E M u)
        (Singular.holomorphicLogCech E M u) (Singular.holomorphicLogCech_cocycle E M u) a).isLocallyConstant.comp (fun z : ℚ => (z : ℂ))⟩

omit [FiniteDimensional ℝ E] in
theorem holomorphicLineNormalizedLogCech_delta :
    Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta (Singular.holomorphicLogCover E M u) 0 1 (holomorphicLineNormalizedLogCech u) =
      holomorphicLineRationalDefectForms u := by
  funext a
  have hdelta := AlgebraicTopology.DeRham.Comparison.SmoothCech.cechDelta_apply (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf E M 0) (Singular.holomorphicLogCover E M u)
    1 (holomorphicLineNormalizedLogCech u) a
  refine hdelta.trans ?_
  rw [Fin.sum_univ_three]
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  let U := Singular.holomorphicLogCover E M u
  let l := Singular.holomorphicLogCech E M u
  let edge := fun j : Fin 3 => LogCech.RationalCech.edgeLog (TopCat.of M) U l j a x
  let hc := Singular.holomorphicLogCech_cocycle E M u a x
  have hs := Logarithms.Construction.logarithmicDefect_spec (edge 2) (edge 0) (edge 1) hc
  have hn := congrArg (fun z : ℂ => holomorphicCurvatureChernScale * z) hs
  rw [holomorphicCurvatureChernScale_period] at hn
  change (1 : ℤ) • (holomorphicCurvatureChernScale * SmoothScalarForm.smoothScalarOpenZeroForm
      (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen (holomorphicLineTransitionLogFunction u (a ∘ (0 : Fin 3).succAbove))) _ v) +
    (-1 : ℤ) • (holomorphicCurvatureChernScale * SmoothScalarForm.smoothScalarOpenZeroForm
      (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen (holomorphicLineTransitionLogFunction u (a ∘ (1 : Fin 3).succAbove))) _ v) +
    (1 : ℤ) • (holomorphicCurvatureChernScale * SmoothScalarForm.smoothScalarOpenZeroForm
      (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen (holomorphicLineTransitionLogFunction u (a ∘ (2 : Fin 3).succAbove))) _ v) = _
  rw [SmoothScalarForm.smoothScalarOpenZeroForm_apply, SmoothScalarForm.smoothScalarOpenZeroForm_apply, SmoothScalarForm.smoothScalarOpenZeroForm_apply]
  change (1 : ℤ) • (holomorphicCurvatureChernScale * edge 0) +
    (-1 : ℤ) • (holomorphicCurvatureChernScale * edge 1) +
    (1 : ℤ) • (holomorphicCurvatureChernScale * edge 2) =
      Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantManifoldZeroForm E _ _ x v
  rw [Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantManifoldZeroForm_apply]
  change _ = (((Logarithms.Construction.logarithmicDefect (edge 2) (edge 0) (edge 1) hc : ℤ) : ℚ) : ℂ)
  push_cast
  simp only [one_smul, neg_one_smul]
  calc
    _ = holomorphicCurvatureChernScale * (edge 2 + edge 0 - edge 1) := by ring
    _ = _ := hn

end

/-! The normalized actual metric curvature and original rational Chern defect have equal Čech–de Rham classes. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M] [T2Space M]
  [IsManifold 𝓘(ℂ, E) ∞ M] (u : Connecting.holomorphicUnitCohomology E M)

theorem holomorphicLineNormalizedCurvature_closed :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (holomorphicLineNormalizedCurvature u) = 0 := by
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (holomorphicCurvatureChernScale • GlobalCurvature.holomorphicLineGlobalCurvature u) = 0
  rw [map_smul, GlobalCurvature.holomorphicLineGlobalCurvature_closed, smul_zero]

def holomorphicLineCurvatureCocycle : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) 2 :=
  ⟨holomorphicLineNormalizedCurvature u,
    (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ 2 _).mpr (holomorphicLineNormalizedCurvature_closed u)⟩

def holomorphicLineCurvatureTotalCocycle :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) (Singular.holomorphicLogCover E M u)) 2 :=
  AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechAugmentationToTotal (E := E) (Singular.holomorphicLogCover E M u)) 2
    (holomorphicLineCurvatureCocycle u)

def holomorphicLineRationalDefectTotal : (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) (Singular.holomorphicLogCover E M u)).X 2 :=
  Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion (Singular.holomorphicLogCover E M u) 2 0 2 rfl (holomorphicLineRationalDefectForms u)

def holomorphicLineCurvatureTotalPrimitive : (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) (Singular.holomorphicLogCover E M u)).X 1 :=
  holomorphicCurvatureChernScale • ComplexMultiplication.HodgeComparison.ConnectionTransgression.CM.Construction.connectionTotalPrimitive (Singular.holomorphicLogCover E M u)
    (holomorphicLineConnectionCech u) (holomorphicLineLogarithmFormCech u)

theorem holomorphicLine_curvature_rational_defect_boundary :
    (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) (Singular.holomorphicLogCover E M u)).d 1 2 (holomorphicLineCurvatureTotalPrimitive u) =
      (holomorphicLineCurvatureTotalCocycle u).val - holomorphicLineRationalDefectTotal u := by
  have hd : holomorphicCurvatureChernScale •
      Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta (Singular.holomorphicLogCover E M u) 0 1 (holomorphicLineLogarithmFormCech u) =
        holomorphicLineRationalDefectForms u :=
    ((Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta (Singular.holomorphicLogCover E M u) 0 1).map_smul holomorphicCurvatureChernScale
      (holomorphicLineLogarithmFormCech u)).symm.trans (holomorphicLineNormalizedLogCech_delta u)
  change (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) (Singular.holomorphicLogCover E M u)).d 1 2
    (holomorphicCurvatureChernScale • ComplexMultiplication.HodgeComparison.ConnectionTransgression.CM.Construction.connectionTotalPrimitive (Singular.holomorphicLogCover E M u)
      (holomorphicLineConnectionCech u) (holomorphicLineLogarithmFormCech u)) = _
  rw [map_smul, holomorphicLine_curvature_logarithmic_boundary, smul_sub, ← map_smul, ← map_smul, hd]
  rfl

theorem holomorphicLineRationalDefectTotal_closed :
    holomorphicLineRationalDefectTotal u ∈ AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) (Singular.holomorphicLogCover E M u)) 2 := by
  let K := Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) (Singular.holomorphicLogCover E M u)
  apply (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff K 2 _).mpr
  have hu := (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff K 2 (holomorphicLineCurvatureTotalCocycle u).val).mp
    (holomorphicLineCurvatureTotalCocycle u).property
  have ht : K.d 2 3 (K.d 1 2 (holomorphicLineCurvatureTotalPrimitive u)) = 0 :=
    ConcreteCategory.congr_hom (K.d_comp_d 1 2 3) (holomorphicLineCurvatureTotalPrimitive u)
  have he : K.d 2 3 ((holomorphicLineCurvatureTotalCocycle u).val - holomorphicLineRationalDefectTotal u) = 0 :=
    (congrArg (K.d 2 3) (holomorphicLine_curvature_rational_defect_boundary u)).symm.trans ht
  rw [map_sub, hu, zero_sub, neg_eq_zero] at he
  exact he

def holomorphicLineRationalDefectCocycle :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) (Singular.holomorphicLogCover E M u)) 2 :=
  ⟨holomorphicLineRationalDefectTotal u, holomorphicLineRationalDefectTotal_closed u⟩

theorem holomorphicLine_curvature_total_class :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) (Singular.holomorphicLogCover E M u)) 2 (holomorphicLineCurvatureTotalCocycle u) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) (Singular.holomorphicLogCover E M u)) 2 (holomorphicLineRationalDefectCocycle u) := by
  apply (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists_succ _ 1 _ _).mpr
  exact ⟨holomorphicLineCurvatureTotalPrimitive u, holomorphicLine_curvature_rational_defect_boundary u⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CurvatureD
