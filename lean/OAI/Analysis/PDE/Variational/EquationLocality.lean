import OAI.Analysis.PDE.Variational.TestDecomposition
import OAI.Analysis.PDE.Variational.LocalizedEquation

open Set Filter _root_.MeasureTheory
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Variational

open OAI.Analysis.PDE.Weak

variable {m : ℕ}

theorem integrable_test_pairing {Ω : Set (CellCoordinates m)}
    {H : CellCoordinates m→CellVectors m} (hH : LocallyIntegrableOn H Ω volume)
    (φ : CellCoordinates m→ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ⊆Ω) : Integrable (fun x ↦ inner ℝ (H x) (cellGradient φ x)) volume := by
  have hi := hH.integrableOn_compact_subset hs hc
  have hg := continuous_cellGradient (hφ.of_le (by simp))
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuousOn hg.continuousOn
  have hon : IntegrableOn (fun x ↦ inner ℝ (H x) (cellGradient φ x)) (tsupport φ) := by
    apply (hi.norm.mul_const C).mono'
      (hi.aestronglyMeasurable.inner hg.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem (isClosed_tsupport φ).measurableSet] with x hx
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg _))
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hon
  intro x hx
  by_contra hnot
  exact hx (by simp [cellGradient_zero_off_tsupport hnot])

theorem integrable_test_load {Ω : Set (CellCoordinates m)}
    {f : CellCoordinates m→ℝ} (hf : LocallyIntegrableOn f Ω volume)
    (φ : CellCoordinates m→ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ⊆Ω) : Integrable (fun x ↦ f x*φ x) volume := by
  have hi := hf.integrableOn_compact_subset hs hc
  have hon := hi.mul_continuousOn hφ.continuousOn hc
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hon
  intro x hx
  exact subset_tsupport φ ((mul_ne_zero_iff.mp hx).2)

theorem cellGradient_sum {ι : Type*} [Fintype ι]
    (ψ : ι→CellCoordinates m→ℝ) (hψ : ∀ i, Differentiable ℝ (ψ i)) (x : CellCoordinates m) :
    cellGradient (fun y ↦ ∑ i, ψ i y) x = ∑ i, cellGradient (ψ i) x := by
  ext j
  simp only [cellGradient_apply, fderiv_fun_sum (fun i _ ↦ hψ i x)]
  simp

theorem weakEquation_of_open_cover {ι : Type*} {Ω : Set (CellCoordinates m)}
    {H : CellCoordinates m→CellVectors m} {f : CellCoordinates m→ℝ}
    (hH : LocallyIntegrableOn H Ω volume) (hf : LocallyIntegrableOn f Ω volume)
    (U : ι→Set (CellCoordinates m)) (hU : ∀ i, IsOpen (U i))
    (hsub : ∀ i, U i⊆Ω) (hcover : Ω⊆⋃ i,U i)
    (hweak : ∀ i, OAI.Analysis.PDE.Weak.WeakDivergenceEquation (U i) H f) : OAI.Analysis.PDE.Weak.WeakDivergenceEquation Ω H f := by
  classical
  intro φ hφ hc hs
  obtain ⟨s,ψ,hψ,heq⟩ := smooth_test_decomposition U hU φ hφ hc (hs.trans hcover)
  have hgrad (x : CellCoordinates m) : cellGradient φ x=∑ i, cellGradient (ψ i) x := by
    rw [heq]
    exact cellGradient_sum ψ (fun i ↦ (hψ i).1.differentiable (by simp)) x
  have hi (i : s) : Integrable (fun x ↦ inner ℝ (H x) (cellGradient (ψ i) x)) volume :=
    integrable_test_pairing hH _ (hψ i).1 (hψ i).2.1 ((hψ i).2.2.trans (hsub i))
  have hj (i : s) : Integrable (fun x ↦ f x*ψ i x) volume :=
    integrable_test_load hf _ (hψ i).1.continuous (hψ i).2.1 ((hψ i).2.2.trans (hsub i))
  calc
    _ = ∫ x, ∑ i:s, inner ℝ (H x) (cellGradient (ψ i) x) := by
      congr 1
      funext x
      rw [hgrad]
      exact inner_sum Finset.univ (fun i:s ↦ cellGradient (ψ i) x) (H x)
    _ = ∑ i:s, ∫ x, inner ℝ (H x) (cellGradient (ψ i) x) :=
      MeasureTheory.integral_finsetSum _ (fun i _ ↦ hi i)
    _ = ∑ i:s, ∫ x, f x*ψ i x := by
      apply Finset.sum_congr rfl
      intro i _
      exact hweak i _ (hψ i).1 (hψ i).2.1 (hψ i).2.2
    _ = ∫ x, ∑ i:s, f x*ψ i x := (MeasureTheory.integral_finsetSum _ (fun i _ ↦ hj i)).symm
    _ = _ := by
      congr 1
      funext x
      rw [← Finset.mul_sum,← congrFun heq x]

theorem weakEquation_of_local {Ω : Set (CellCoordinates m)}
    {H : CellCoordinates m→CellVectors m} {f : CellCoordinates m→ℝ}
    (hH : LocallyIntegrableOn H Ω volume) (hf : LocallyIntegrableOn f Ω volume)
    (hloc : ∀ x∈Ω, ∃ U, IsOpen U ∧ x∈U ∧ U⊆Ω ∧ OAI.Analysis.PDE.Weak.WeakDivergenceEquation U H f) :
    OAI.Analysis.PDE.Weak.WeakDivergenceEquation Ω H f := by
  choose U hU hmem hsub hweak using fun x:Ω ↦ hloc x x.property
  apply weakEquation_of_open_cover hH hf U hU hsub _ hweak
  intro x hx
  exact mem_iUnion.mpr ⟨⟨x,hx⟩,hmem ⟨x,hx⟩⟩

end OAI.Analysis.PDE.Variational
