import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiSchwartzTests
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CutoffCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Insertion
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChartFrameTests

/-! # Schwartz Test Cutoff -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SchwartzTestCutoff

noncomputable section

section

/-! The actual global cutoff used for chart insertion equals one on the support of every inserted test. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
  (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))

theorem holomorphicSchwartzFrameCutoff_one_on_image (x : V.analyticSpace)
    (hx : x ∈ ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e (tsupport g)) :
    AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs x = 1 := by
  obtain ⟨z, hz, rfl⟩ := hx
  exact AntiSchwartzTests.holomorphicSchwartzFrameCutoff_one V u e he i g hg hs z hz

theorem holomorphicLineAntiSchwartzFrameInsertion_cutoff
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)) :
    SupportedForms.holomorphicLineSmoothMul u ⊤ 1 (AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs)
      (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
      (AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c).val =
      (AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c).val := by
  apply Subtype.ext
  funext j
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  rw [SupportedForms.holomorphicLineSmoothMul_apply]
  by_cases hx : x.val ∈ ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e (tsupport g)
  · rw [holomorphicSchwartzFrameCutoff_one_on_image V u e he i g hg hs x.val hx, one_smul]
  · rw [AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion_zero V u e he i g hg hs c j x hx]
    exact smul_zero (A := TangentSpace 𝓘(ℝ, V.analyticModel) x.val [⋀^Fin 1]→L[ℝ] ℂ)
      (AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs x.val)

end

section

/-! Actual outer cutoff multiplication fixes each original form already cut off inside its one region. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem complex_smul_fix_inner {F : Type*} [AddCommMonoid F] [Module ℂ F]
    (r s : ℂ) (a : F) (h : s ≠ 0 → r = 1) : r • (s • a) = s • a := by
  by_cases hs : s = 0
  · rw [hs, zero_smul, smul_zero]
  · rw [h hs, one_smul]

theorem holomorphicLineCutoffAntiForm_nested (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (g : V.analyticSpace → ℂ) (hg : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ g)
    (hone : ∀ x ∈ tsupport g, f x = 1) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V g hg a) =
      HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V g hg a := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  simp only [HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm, SupportedForms.holomorphicLineSmoothMul_apply]
  exact complex_smul_fix_inner (f x) (g x) (a.val.val i x) (fun hgx => hone x (subset_tsupport g hgx))

theorem holomorphicLineCutoffAntiForm_of_fixed_inner (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (g : V.analyticSpace → ℂ) (hg : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ g)
    (hone : ∀ x ∈ tsupport g, f x = 1) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (ha : HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V g hg a = a) :
    HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a = a :=
  (congrArg (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf) ha.symm).trans
    ((holomorphicLineCutoffAntiForm_nested V f hf g hg hone a).trans ha)

theorem holomorphicLineAntiSchwartzFrameInsertion_cutoff_anti (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)) :
    HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V (AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs)
      (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
      (AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c) =
        AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c :=
  Subtype.ext (holomorphicLineAntiSchwartzFrameInsertion_cutoff V u e he i g hg hs c)

end

/-! Inserting the original extracted frame test reconstructs exactly the original nested scalar multiplications. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem holomorphicLineSmoothMul_nested (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (n : ℕ)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (g : V.analyticSpace → ℂ) (hg : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ g)
    (hone : ∀ x ∈ tsupport g, f x = 1) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf (SupportedForms.holomorphicLineSmoothMul u ⊤ n g hg a) =
      SupportedForms.holomorphicLineSmoothMul u ⊤ n g hg a := by
  apply HolomorphicLine.AntiForms.holomorphicLineSmoothForm_ext
  intro i x
  simp only [SupportedForms.holomorphicLineSmoothMul_apply]
  exact complex_smul_fix_inner (f x) (g x) (a.val i x) (fun hgx => hone x (subset_tsupport g hgx))

theorem holomorphicLineSmoothFrameInsertion_chart_test (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (i : V.analyticSpace) (n : ℕ)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Set V.analyticSpace))
    (g : V.analyticSpace → ℂ) (hg : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ g)
    (hsg : tsupport g ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    HolomorphicFrame.Insertion.holomorphicLineSmoothFrameInsertion u i n f hf hsf (ChartFrameTests.holomorphicLineChartFrameTest V u e i n g hg hsg a) =
      SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf (SupportedForms.holomorphicLineSmoothMul u ⊤ n g hg a) := by
  apply HolomorphicLine.AntiForms.holomorphicLineSmoothForm_ext
  intro j x
  by_cases hx : x.val ∈ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i
  · rw [HolomorphicFrame.Insertion.holomorphicLineSmoothFrameInsertion_apply u i n f hf hsf _ j x hx,
      ChartFrameTests.holomorphicLineChartFrameTest_apply V u e i n g hg hsg a ⟨x.val, hx⟩,
      SupportedForms.holomorphicLineSmoothMul_apply, SupportedForms.holomorphicLineSmoothMul_apply,
      smul_comm ((CohomologyTransitions.holomorphicCohomologyTransition V.analyticModel V.analyticSpace u i j).val
        ⟨x.val, hx, x.property.2⟩) (g x.val),
      ← a.property i j x.val x.property.1 hx x.property.2]
  · rw [HolomorphicFrame.Insertion.holomorphicLineSmoothFrameInsertion_zero u i n f hf hsf _ j x (fun ht => hx (hsf ht)),
      SupportedForms.holomorphicLineSmoothMul_apply, image_eq_zero_of_notMem_tsupport (fun ht => hx (hsf ht))]
    exact (zero_smul ℂ ((SupportedForms.holomorphicLineSmoothMul u ⊤ n g hg a).val j x)).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SchwartzTestCutoff
