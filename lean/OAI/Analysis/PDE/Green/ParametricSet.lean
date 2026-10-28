import OAI.Analysis.PDE.Green.ParametricIntegral

/-! Smooth set integrals over a measurable subset of a fixed compact set.
No null-boundary assumption or artificial extension across the compact set is
required: its interior measure is pulled back to the compact subtype. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set _root_.MeasureTheory
open scoped ContDiff Topology

universe u
variable {E A F : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [SecondCountableTopology A]
  [MeasurableSpace A] [BorelSpace A]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem contDiffOn_compact_setIntegral (μ : Measure A) {K S : Set A}
    (hK : IsCompact K) (_ : MeasurableSet S) (hSK : S ⊆ K) (hμK : μ K < ⊤)
    {U : Set E} (hU : IsOpen U) {Ω : Set (E × A)} (hΩ : IsOpen Ω)
    (f : E × A → F) (hf : ContDiffOn ℝ ∞ f Ω)
    (hdom : ∀ x ∈ U, ∀ t ∈ K, (x, t) ∈ Ω) :
    ContDiffOn ℝ ∞ (fun x => ∫ t in S, f (x, t) ∂μ) U := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : IsFiniteMeasure (μ.restrict S) := ⟨by
    simpa only [Measure.restrict_apply_univ] using (measure_mono hSK).trans_lt hμK⟩
  let ν : Measure K := (μ.restrict S).comap Subtype.val
  have hh := contDiffOn_compact_parametric_integral (μ := ν) hU hΩ f hf
    (fun t : K => (t : A)) continuous_subtype_val (fun x hx t => hdom x hx t t.property)
  have he : (fun x => ∫ t : K, f (x, (t : A)) ∂ν) =
      (fun x => ∫ t in S, f (x, t) ∂μ) := by
    funext x
    have h := integral_subtype_comap (μ := μ.restrict S) hK.isClosed.measurableSet
      (fun t : A => f (x, t))
    simpa only [ν, Measure.restrict_restrict hK.isClosed.measurableSet,
      inter_eq_right.mpr hSK] using! h
  rw [he] at hh
  exact hh

end OAI.Analysis.PDE.Green
