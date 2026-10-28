import OAI.Analysis.PDE.Variational.ExtensionMap
import OAI.Analysis.PDE.Weak.Elliptic.Cutoff

open Set Filter _root_.MeasureTheory
open scoped ContDiff Topology
noncomputable section

namespace OAI.Analysis.PDE.Variational

open OAI.Analysis.PDE.Weak

variable {m : ℕ}

def periodicH1Pair (a b : CellCoordinates m) (Ω P : Set (CellCoordinates m)) :
    PeriodicH10 a b Ω P →L[ℝ] OAI.Analysis.PDE.Weak.H1Pair m :=
  ((cellZeroExtensionL2 a b).comp (periodicValue a b Ω P)).prod
    ((cellZeroExtensionL2 a b).comp (testGradientMap a b Ω P).range.topologicalClosure.subtypeL)

theorem periodicH1Pair_value_ae (a b : CellCoordinates m) (Ω P : Set (CellCoordinates m))
    (u : PeriodicH10 a b Ω P) :
    (periodicH1Pair a b Ω P u).1 =ᵐ[volume] cellZeroExtension a b (periodicValue a b Ω P u) :=
  cellZeroExtensionL2_ae a b _

theorem periodicH1Pair_gradient_ae (a b : CellCoordinates m) (Ω P : Set (CellCoordinates m))
    (u : PeriodicH10 a b Ω P) :
    (periodicH1Pair a b Ω P u).2 =ᵐ[volume] cellZeroExtension a b u.val :=
  cellZeroExtensionL2_ae a b _

theorem cellZeroExtension_cellToL2 {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (a b : CellCoordinates m) (f : CellCoordinates m → H) (hf : Continuous f) :
    cellZeroExtensionL2 a b (cellToL2 a b f hf) =ᵐ[volume] (Icc a b).indicator f := by
  have h := (ae_restrict_iff' measurableSet_Icc).mp (memLp_continuous_cell a b hf).coeFn_toLp
  filter_upwards [cellZeroExtensionL2_ae a b (cellToL2 a b f hf), h] with x hx hy
  rw [hx]
  by_cases hxc : x∈Icc a b
  · simpa only [cellZeroExtension, indicator_of_mem hxc, cellToL2] using hy hxc
  · simp [cellZeroExtension, hxc]

theorem periodicH1Pair_test_value_ae (a b : CellCoordinates m) (hab : a≤b)
    (Ω P : Set (CellCoordinates m)) (k : Fin (m+1))
    (hface : ∀ y ∈ Icc (a ∘ k.succAbove) (b ∘ k.succAbove), k.insertNth (b k) y ∉ Ω)
    (u : PeriodicTests Ω P) :
    (periodicH1Pair a b Ω P (periodicTestEmbedding a b Ω P u)).1 =ᵐ[volume]
      (Icc a b).indicator u.val := by
  change cellZeroExtensionL2 a b (periodicValue a b Ω P (periodicTestEmbedding a b Ω P u)) =ᵐ[volume] _
  rw [periodicValue_test a b hab Ω P k hface]
  exact cellZeroExtension_cellToL2 a b u.val (periodicTest_contDiff u).continuous

theorem periodicH1Pair_test_gradient_ae (a b : CellCoordinates m)
    (Ω P : Set (CellCoordinates m)) (u : PeriodicTests Ω P) :
    (periodicH1Pair a b Ω P (periodicTestEmbedding a b Ω P u)).2 =ᵐ[volume]
      (Icc a b).indicator (cellGradient u.val) :=
  cellZeroExtension_cellToL2 a b _ (continuous_cellGradient (periodicTest_contDiff_one u))

theorem cellGradient_zero_off_tsupport {η : CellCoordinates m → ℝ} {x : CellCoordinates m}
    (hx : x∉tsupport η) : cellGradient η x = 0 := by
  ext i
  simp [cellGradient_apply, fderiv_of_notMem_tsupport ℝ hx]

theorem cutoff_periodicH1Pair_test (a b : CellCoordinates m) (hab : a≤b)
    (Ω P : Set (CellCoordinates m)) (k : Fin (m+1))
    (hface : ∀ y ∈ Icc (a ∘ k.succAbove) (b ∘ k.succAbove), k.insertNth (b k) y ∉ Ω)
    (η : CellCoordinates m → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hcell : tsupport η ⊆ Icc a b)
    {M K : ℝ} (hM : ∀ x, |η x|≤M) (hK : ∀ x, ‖cellGradient η x‖≤K)
    (u : PeriodicTests Ω P) :
    OAI.Analysis.PDE.Weak.cutoffH1Pair η (hη.of_le (by simp)) hM hK
      (periodicH1Pair a b Ω P (periodicTestEmbedding a b Ω P u)) =
      OAI.Analysis.PDE.Weak.smoothH1Pair (fun x ↦ η x * u.val x) (hη.mul (periodicTest_contDiff u)) hc.mul_right := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [OAI.Analysis.PDE.Weak.cutoffH1Pair_value_ae η (hη.of_le (by simp)) hM hK
      (periodicH1Pair a b Ω P (periodicTestEmbedding a b Ω P u)),
      periodicH1Pair_test_value_ae a b hab Ω P k hface u,
      OAI.Analysis.PDE.Weak.smoothH1Pair_value_ae (fun x ↦ η x*u.val x) (hη.mul (periodicTest_contDiff u)) hc.mul_right]
      with x hx hy hz
    rw [hx, hy, hz]
    by_cases hxc : x∈Icc a b
    · simp [hxc]
    · have he : η x=0 := by
        by_contra hne
        exact hxc (hcell (subset_tsupport _ hne))
      simp [hxc, he]
  · apply Lp.ext
    filter_upwards [OAI.Analysis.PDE.Weak.cutoffH1Pair_gradient_ae η (hη.of_le (by simp)) hM hK
      (periodicH1Pair a b Ω P (periodicTestEmbedding a b Ω P u)),
      periodicH1Pair_test_value_ae a b hab Ω P k hface u,
      periodicH1Pair_test_gradient_ae a b Ω P u,
      OAI.Analysis.PDE.Weak.smoothH1Pair_gradient_ae (fun x ↦ η x*u.val x) (hη.mul (periodicTest_contDiff u)) hc.mul_right]
      with x hx hy hz hw
    rw [hx, hy, hz, hw,
      OAI.Analysis.PDE.Weak.cellGradient_mul (hη.differentiable (by simp)) ((periodicTest_contDiff u).differentiable (by simp))]
    by_cases hxc : x∈Icc a b
    · simp [hxc]
    · have hout : x∉tsupport η := fun h ↦ hxc (hcell h)
      have he : η x=0 := by
        by_contra hne
        exact hout (subset_tsupport _ hne)
      simp [hxc, he, cellGradient_zero_off_tsupport hout]

/-- Every compactly localized variational solution belongs to the genuine smooth
H¹ graph closure; no weak-to-strong approximation theorem is assumed. -/
theorem cutoff_periodicH1Pair_mem_H1Zero (a b : CellCoordinates m) (hab : a≤b)
    (Ω P : Set (CellCoordinates m)) (k : Fin (m+1))
    (hface : ∀ y ∈ Icc (a ∘ k.succAbove) (b ∘ k.succAbove), k.insertNth (b k) y ∉ Ω)
    (η : CellCoordinates m → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hcell : tsupport η ⊆ Icc a b)
    {M K : ℝ} (hM : ∀ x, |η x|≤M) (hK : ∀ x, ‖cellGradient η x‖≤K)
    {Ω' : Set (CellCoordinates m)} (hΩ' : tsupport η ⊆ Ω') (u : PeriodicH10 a b Ω P) :
    OAI.Analysis.PDE.Weak.cutoffH1Pair η (hη.of_le (by simp)) hM hK (periodicH1Pair a b Ω P u) ∈ OAI.Analysis.PDE.Weak.H1Zero Ω' := by
  have hclosed : IsClosed {v : PeriodicH10 a b Ω P |
      OAI.Analysis.PDE.Weak.cutoffH1Pair η (hη.of_le (by simp)) hM hK (periodicH1Pair a b Ω P v) ∈ OAI.Analysis.PDE.Weak.H1Zero Ω'} :=
    isClosed_closure.preimage ((OAI.Analysis.PDE.Weak.cutoffH1Pair η (hη.of_le (by simp)) hM hK).continuous.comp
      (periodicH1Pair a b Ω P).continuous)
  apply closure_minimal (s := Set.range (periodicTestEmbedding a b Ω P)) ?_ hclosed
    (denseRange_periodicTestEmbedding a b Ω P u)
  rintro v ⟨t, rfl⟩
  change OAI.Analysis.PDE.Weak.cutoffH1Pair η _ hM hK (periodicH1Pair a b Ω P (periodicTestEmbedding a b Ω P t)) ∈ OAI.Analysis.PDE.Weak.H1Zero Ω'
  rw [cutoff_periodicH1Pair_test a b hab Ω P k hface η hη hc hcell hM hK t]
  apply OAI.Analysis.PDE.Weak.smoothH1Pair_mem_H1Zero
  exact fun x hx ↦ hΩ' (tsupport_mul_subset_left hx)

end OAI.Analysis.PDE.Variational
