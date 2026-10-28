import OAI.RepresentationTheory.Weil.AdelicSplitting.DenseHilbert
import OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanFourier

/-! # Dense Extension -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.DenseExtension.Construction

noncomputable section

/-! Norm identities and pointwise coefficient formulas pass from a dense
linear test space to its bounded L² extension. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology InnerProductSpace

variable {S H V : Type*} [AddCommGroup S] [Module ℂ S]
variable [NormedAddCommGroup H] [NormedSpace ℂ H]
variable [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable (P : S →ₗ[ℂ] H) (hP : DenseRange P)

include hP

omit [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] in
theorem dense_linear_test_sequence (x : H) :
    ∃ f : ℕ → S, Tendsto (fun j => P (f j)) atTop (𝓝 x) := by
  obtain ⟨y, hy, ht⟩ := mem_closure_iff_seq_limit.mp (hP x)
  choose f hf using hy
  exact ⟨f, by simpa only [hf] using ht⟩

theorem dense_linear_extension_norm_sq (A : S →ₗ[ℂ] V) (C c : ℝ)
    (hbound : ∀ f, ‖A f‖ ≤ C * ‖P f‖)
    (hnorm : ∀ f, ‖A f‖ ^ 2 = c * ‖P f‖ ^ 2) (x : H) :
    ‖A.extendOfNorm P x‖ ^ 2 = c * ‖x‖ ^ 2 := by
  obtain ⟨f, hf⟩ := dense_linear_test_sequence P hP x
  have he (j : ℕ) : A.extendOfNorm P (P (f j)) = A (f j) :=
    LinearMap.extendOfNorm_eq hP ⟨C, hbound⟩ (f j)
  have ht := ((A.extendOfNorm P).continuous.tendsto x).comp hf
  apply tendsto_nhds_unique (ht.norm.pow 2)
  exact ((hf.norm.pow 2).const_mul c).congr (fun j => by simp only [Function.comp_apply, he, hnorm])

omit [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] in
theorem dense_linear_extension_ae {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A : S →ₗ[ℂ] Lp ℂ 2 μ) (C : ℝ)
    (hbound : ∀ f, ‖A f‖ ≤ C * ‖P f‖)
    (K : H → X → ℂ) (hK : ∀ v, Continuous (fun x => K x v))
    (hae : ∀ f, A f =ᵐ[μ] K (P f)) (x : H) :
    A.extendOfNorm P x =ᵐ[μ] K x := by
  obtain ⟨f, hf⟩ := dense_linear_test_sequence P hP x
  have he (j : ℕ) : A.extendOfNorm P (P (f j)) = A (f j) :=
    LinearMap.extendOfNorm_eq hP ⟨C, hbound⟩ (f j)
  have ht : Tendsto (fun j => A (f j)) atTop (𝓝 (A.extendOfNorm P x)) := by
    simpa only [Function.comp_def, he] using ((A.extendOfNorm P).continuous.tendsto x).comp hf
  obtain ⟨s, hs, hsae⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  filter_upwards [hsae, ae_all_iff.mpr (fun j => hae (f j))] with v hv hev
  apply tendsto_nhds_unique hv
  exact ((((hK v).tendsto x).comp hf).comp hs.tendsto_atTop).congr
    (fun j => (hev (s j)).symm)

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.DenseExtension.Construction
