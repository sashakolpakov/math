import OAI.AlgebraicGeometry.Comparison.Betti.Open.SmoothForms
import OAI.AlgebraicGeometry.Cycles.Functoriality.AnalyticInverse
import OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree

/-! # Holomorphic Sections -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HolomorphicSections.Kaehler

noncomputable section

/-! Regular functions on actual analytic opens are holomorphic, and their
real de Rham differentials have the genuine (1,0) character. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.Topology
open OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree OAI.AlgebraicGeometry.Comparison.Betti.Open.SmoothForms

attribute [local instance] Comparison.Betti.Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem openPointHomeomorph_symm_holomorphic (U : X.left.Opens) [Nonempty U] :
    ContMDiff 𝓘(ℂ, Comparison.Betti.RegularSmoothness.NativeModel X) 𝓘(ℂ, Comparison.Betti.RegularSmoothness.NativeModel (Comparison.Betti.Open.AffineIsoEvaluation.openOver X U)) ∞
      (Comparison.Betti.Open.AffineIsoEvaluation.openPointHomeomorph X U).symm := by
  let f := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Comparison.Betti.Open.AffineIsoEvaluation.openInclusion X U)
  let g := (Comparison.Betti.Open.AffineIsoEvaluation.openPointHomeomorph X U).symm
  have hf : IsLocalDiffeomorph 𝓘(ℂ, Comparison.Betti.RegularSmoothness.NativeModel (Comparison.Betti.Open.AffineIsoEvaluation.openOver X U)) 𝓘(ℂ, Comparison.Betti.RegularSmoothness.NativeModel X) ω f := by
    intro p
    exact Cycles.Functoriality.AnalyticInverse.Construction.isLocalDiffeomorphAt_of_bijective_mfderiv _
      (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (Comparison.Betti.Open.AffineIsoEvaluation.openInclusion X U) ω) p
      (ComplexPoints.Analytic.IntrinsicOpenDifferential.mfderiv_nativeScheme_openImmersion_bijective (Comparison.Betti.Open.AffineIsoEvaluation.openInclusion X U) p)
  have he : f ∘ g = (Subtype.val : Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := by
    funext p
    exact (Comparison.Betti.Open.AffineIsoEvaluation.openPointHomeomorph_val X U (g p)).symm.trans
      (congrArg Subtype.val ((Comparison.Betti.Open.AffineIsoEvaluation.openPointHomeomorph X U).apply_symm_apply p))
  have hfg : ContMDiff 𝓘(ℂ, Comparison.Betti.RegularSmoothness.NativeModel X) 𝓘(ℂ, Comparison.Betti.RegularSmoothness.NativeModel X) ∞ (f ∘ g) := by
    rw [he]
    exact contMDiff_subtype_val
  intro p
  have hs := ((hf (g p)).localInverse_contMDiffAt.of_le
    (show (∞ : ℕ∞ω) ≤ ω from le_top)).comp p (hfg p)
  have hloc := (hf (g p)).localInverse_eventuallyEq_left.comp_tendsto
    (g.continuous.continuousAt : Filter.Tendsto g (nhds p) (nhds (g p)))
  exact hs.congr_of_eventuallyEq hloc.symm

theorem sectionEvaluationOn_holomorphic (U : X.left.Opens) (a : Γ(X.left, U)) :
    ContMDiff 𝓘(ℂ, Comparison.Betti.RegularSmoothness.NativeModel X) 𝓘(ℂ, ℂ) ∞ (Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn X U a) := by
  classical
  by_cases hU : Nonempty U
  · let : Nonempty U := hU
    exact (Comparison.Betti.RegularSmoothness.globalEvaluation_contMDiff (Comparison.Betti.Open.AffineIsoEvaluation.openOver X U) (U.topIso.inv a) ∞).comp
      (openPointHomeomorph_symm_holomorphic X U)
  · intro p
    exact (hU ⟨⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p.val, p.property⟩⟩).elim

section PureDifferential

variable {F M A : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace M] [ChartedSpace F M]
  [IsManifold 𝓘(ℝ, F) ∞ M] [IsManifold 𝓘(ℂ, F) ∞ M]
  [CommRing A] [Algebra ℂ A]
  (φ : A →ₐ[ℂ] C(M, ℂ))
  (hφ : ∀ a, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℂ) ∞ (φ a))
  (hc : ∀ a, ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, ℂ) ∞ (φ a))

include hc in
theorem regularDifferential_pure (a : A) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree F M 1 0
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Comparison.Betti.Smooth.FormRealization.zeroFormMap φ hφ a)).val := by
  intro e he y hy
  have hs : ContMDiffAt 𝓘(ℂ, F) 𝓘(ℂ, F) ∞ e.symm y :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hy
  have hd : DifferentiableAt ℂ (fun z => φ a (e.symm z)) y :=
    ((hc a).contMDiffAt.comp y hs).contDiffAt.differentiableAt (by simp)
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart _ e he hy]
  change Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree F 1 0
    (extDeriv ((Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar (φ a)).inChart e) y)
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar_inChart, extDeriv_constOfIsEmpty, hd.fderiv_restrictScalars ℝ]
  intro z v
  change fderiv ℂ (fun z => φ a (e.symm z)) y ((z : ℂ) • v 0) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 0 z * fderiv ℂ (fun z => φ a (e.symm z)) y (v 0)
  simp [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter]

include hc in
theorem algebraicOneForm_pure (a : Comparison.Betti.Algebraic.Forms.Form A 1) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree F M 1 0 (Comparison.Betti.Smooth.FormRealization.oneFormMap φ hφ a).val := by
  have hsymbol (b : Fin 2 → A) : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree F M 1 0
      (Comparison.Betti.Smooth.FormRealization.oneFormMap φ hφ (Comparison.Betti.Algebraic.Forms.formSymbol A b)).val := by
    rw [Comparison.Betti.Smooth.FormRealization.oneFormMap_symbol]
    intro e he y hy
    change Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree F 1 0
      ((Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction (φ (b 0))
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Comparison.Betti.Smooth.FormRealization.zeroFormMap φ hφ (b 1))).val).inChart e y)
    rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smulFunction]
    exact (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule F 1 0).smul_mem _
      (regularDifferential_pure φ hφ hc (b 1) e he y hy)
  obtain ⟨r, rfl⟩ := (Comparison.Betti.Algebraic.Forms.relations A 1).mkQ_surjective a
  induction r using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero]
    exact Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree.zero
  | add r t hr ht =>
    simp only [map_add]
    exact hr.add ht
  | single b c =>
    have he : Finsupp.single b c = c • Comparison.Betti.Algebraic.Forms.symbol A b := by
      simp [Comparison.Betti.Algebraic.Forms.symbol]
    rw [he]
    simp only [map_smul]
    exact (hsymbol b).const_smul c

end PureDifferential

variable {F M A : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace M] [ChartedSpace F M]
  [IsManifold 𝓘(ℝ, F) ∞ M] [IsManifold 𝓘(ℂ, F) ∞ M]
  [CommRing A] [Algebra ℂ A]
  (φ : A →ₐ[ℂ] C(M, ℂ))
  (hφ : ∀ a, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℂ) ∞ (φ a))
  (hc : ∀ a, ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, ℂ) ∞ (φ a))

include hc in
theorem algebraicTwoForm_pure (a : Comparison.Betti.Algebraic.Forms.Form A 2) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree F M 2 0 (Comparison.Betti.Smooth.CochainMap.smoothFormMap φ hφ 2 a).val := by
  have hsymbol (b : Fin 3 → A) : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree F M 2 0
      (Comparison.Betti.Smooth.CochainMap.smoothFormMap φ hφ 2 (Comparison.Betti.Algebraic.Forms.formSymbol A b)).val := by
    rw [Comparison.Betti.Smooth.CochainMap.smoothFormMap_symbol, Comparison.Betti.HigherSmoothSymbols.smoothSymbol_succ]
    have hfirst : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree F M 1 0 (Comparison.Betti.HigherSmoothSymbols.smoothSymbol φ hφ 1 (Fin.init b)).val := by
      rw [← Comparison.Betti.Smooth.CochainMap.smoothFormMap_symbol, Comparison.Betti.Smooth.CochainMap.smoothFormMap_one]
      exact algebraicOneForm_pure φ hφ hc _
    exact AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.hasManifoldBidegree_wedge hfirst (regularDifferential_pure φ hφ hc _)
  obtain ⟨r, rfl⟩ := (Comparison.Betti.Algebraic.Forms.relations A 2).mkQ_surjective a
  induction r using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero]
    exact Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree.zero
  | add r t hr ht =>
    simp only [map_add]
    exact hr.add ht
  | single b c =>
    have he : Finsupp.single b c = c • Comparison.Betti.Algebraic.Forms.symbol A b := by
      simp [Comparison.Betti.Algebraic.Forms.symbol]
    rw [he]
    simp only [map_smul]
    exact (hsymbol b).const_smul c

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HolomorphicSections.Kaehler
