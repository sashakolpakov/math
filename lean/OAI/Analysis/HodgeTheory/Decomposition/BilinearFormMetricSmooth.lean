import OAI.Analysis.HodgeTheory.Decomposition.BilinearFormMetric
import OAI.Analysis.HodgeTheory.Decomposition.MetricCoefficients

/-! # Bilinear Form Metric Smooth -/

namespace OAI.Analysis.HodgeTheory.Decomposition.BilinearFormMetricSmooth.Constructions

noncomputable section

/-! Smoothness of the explicit general covector metric wherever its
exterior Gram matrix is nonsingular. -/

open scoped ContDiff

variable {E D ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [Fintype ι] [LinearOrder ι]

omit [Fintype ι] in
theorem bilinearExteriorGram_entry_smooth (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : D → E →L[ℝ] E →L[ℝ] ℝ) {U : Set D} (hB : ContDiffOn ℝ ∞ B U)
    (s t : Set.powersetCard ι n) : ContDiffOn ℝ ∞ (fun x => BilinearFormMetric.Constructions.bilinearExteriorGram b n (B x) s t) U := by
  apply MetricCoefficients.Constructions.matrixDet_smoothOn
  intro i j
  exact (hB.clm_apply contDiffOn_const).clm_apply contDiffOn_const

theorem bilinearFormMetricPair_smoothOn (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : D → E →L[ℝ] E →L[ℝ] ℝ) (a c : D → DifferentialForms.Manifold.Basic.FormValue E n) {U : Set D}
    (hB : ContDiffOn ℝ ∞ B U) (ha : ContDiffOn ℝ ∞ a U) (hc : ContDiffOn ℝ ∞ c U)
    (hdet : ∀ x ∈ U, (BilinearFormMetric.Constructions.bilinearExteriorGram b n (B x)).det ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (a x) (c x)) U := by
  have hevala (s : Set.powersetCard ι n) := MetricCoefficients.Constructions.smooth_fixed_form_evaluation n (BilinearFormMetric.Constructions.basisExteriorTuple b n s) ha
  have hevalc (s : Set.powersetCard ι n) := MetricCoefficients.Constructions.smooth_fixed_form_evaluation n (BilinearFormMetric.Constructions.basisExteriorTuple b n s) hc
  have hcoeff (s t : Set.powersetCard ι n) :
      ContDiffOn ℝ ∞ (fun x => ((BilinearFormMetric.Constructions.bilinearExteriorGram b n (B x))⁻¹ s t : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (MetricCoefficients.Constructions.matrixInverse_entry_smoothOn
      (fun x => BilinearFormMetric.Constructions.bilinearExteriorGram b n (B x)) (bilinearExteriorGram_entry_smooth b n B hB) hdet s t)
  have hconj : ContDiff ℝ ∞ (star : ℂ → ℂ) := Complex.conjCLE.contDiff
  unfold BilinearFormMetric.Constructions.bilinearFormMetricPair
  fun_prop

theorem bilinearFormMetricPair_joint_contDiffAt (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a c : DifferentialForms.Manifold.Basic.FormValue E n) (hdet : (BilinearFormMetric.Constructions.bilinearExteriorGram b n B).det ≠ 0) :
    ContDiffAt ℝ ∞
      (fun x : (E →L[ℝ] E →L[ℝ] ℝ) × DifferentialForms.Manifold.Basic.FormValue E n × DifferentialForms.Manifold.Basic.FormValue E n =>
        BilinearFormMetric.Constructions.bilinearFormMetricPair b n x.1 x.2.1 x.2.2) (B, a, c) := by
  let U := {x : (E →L[ℝ] E →L[ℝ] ℝ) × DifferentialForms.Manifold.Basic.FormValue E n × DifferentialForms.Manifold.Basic.FormValue E n |
    (BilinearFormMetric.Constructions.bilinearExteriorGram b n x.1).det ≠ 0}
  have hcont : Continuous (fun x : (E →L[ℝ] E →L[ℝ] ℝ) × DifferentialForms.Manifold.Basic.FormValue E n × DifferentialForms.Manifold.Basic.FormValue E n =>
      (BilinearFormMetric.Constructions.bilinearExteriorGram b n x.1).det) := by
    have hsdet : ContDiff ℝ ∞ (fun x : (E →L[ℝ] E →L[ℝ] ℝ) × DifferentialForms.Manifold.Basic.FormValue E n × DifferentialForms.Manifold.Basic.FormValue E n =>
        (BilinearFormMetric.Constructions.bilinearExteriorGram b n x.1).det) := by
      apply contDiffOn_univ.mp
      apply MetricCoefficients.Constructions.matrixDet_smoothOn
      exact bilinearExteriorGram_entry_smooth b n _ contDiffOn_fst
    exact hsdet.continuous
  have hU : IsOpen U := isOpen_ne_fun hcont continuous_const
  have hs : ContDiffOn ℝ ∞
      (fun x : (E →L[ℝ] E →L[ℝ] ℝ) × DifferentialForms.Manifold.Basic.FormValue E n × DifferentialForms.Manifold.Basic.FormValue E n =>
        BilinearFormMetric.Constructions.bilinearFormMetricPair b n x.1 x.2.1 x.2.2) U :=
    bilinearFormMetricPair_smoothOn b n _ _ _ contDiffOn_fst contDiffOn_snd.fst contDiffOn_snd.snd
      (fun _ hx => hx)
  exact hs.contDiffAt (hU.mem_nhds hdet)

end

end OAI.Analysis.HodgeTheory.Decomposition.BilinearFormMetricSmooth.Constructions
