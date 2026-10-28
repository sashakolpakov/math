import OAI.Analysis.PDE.Variational.ZeroTraceApproximation
import OAI.Analysis.PDE.Variational.PeriodicH1Equation

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Variational

open OAI.Analysis.PDE.Weak

variable {m : ℕ}

/-- Compact localization preserves the genuine zero-Dirichlet graph closure,
even when the localization meets the boundary of the domain. -/
theorem cutoff_periodicH1Pair_mem_H1Zero_domain
    (a b : CellCoordinates m) (hab : a≤b) (Ω P : Set (CellCoordinates m))
    (k : Fin (m+1))
    (hface : ∀ y∈Icc (a∘k.succAbove) (b∘k.succAbove), k.insertNth (b k) y∉Ω)
    (η : CellCoordinates m→ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hcell : tsupport η⊆Icc a b)
    {M K : ℝ} (hM : ∀x,|η x|≤M) (hK : ∀x,‖cellGradient η x‖≤K)
    (u : PeriodicH10 a b Ω P) :
    OAI.Analysis.PDE.Weak.cutoffH1Pair η (hη.of_le (by simp)) hM hK (periodicH1Pair a b Ω P u)∈OAI.Analysis.PDE.Weak.H1Zero Ω := by
  have hclosed : IsClosed {v : PeriodicH10 a b Ω P |
      OAI.Analysis.PDE.Weak.cutoffH1Pair η (hη.of_le (by simp)) hM hK (periodicH1Pair a b Ω P v)∈OAI.Analysis.PDE.Weak.H1Zero Ω} :=
    isClosed_closure.preimage ((OAI.Analysis.PDE.Weak.cutoffH1Pair η (hη.of_le (by simp)) hM hK).continuous.comp
      (periodicH1Pair a b Ω P).continuous)
  apply closure_minimal (s:=range (periodicTestEmbedding a b Ω P)) ?_ hclosed
    (denseRange_periodicTestEmbedding a b Ω P u)
  rintro v ⟨t,rfl⟩
  change OAI.Analysis.PDE.Weak.cutoffH1Pair η _ hM hK (periodicH1Pair a b Ω P (periodicTestEmbedding a b Ω P t))∈OAI.Analysis.PDE.Weak.H1Zero Ω
  rw [cutoff_periodicH1Pair_test a b hab Ω P k hface η hη hc hcell hM hK t]
  apply smooth_zero_extension_mem_H1Zero
  intro x hx
  rw [t.property.2.1 x hx,mul_zero]

/-- The actual periodic weak solution has a genuine zero-boundary H¹
representative near every point of the transverse slab, including lateral
boundary points and intersections with fundamental-cell seams. -/
theorem periodicRepresentative_boundary_H1_equation
    (J : Finset (Fin (m+1))) (a b : CellCoordinates m) (hab : a≤b)
    (hL : ∀ i∈J, a i<b i) (Ω : Set (CellCoordinates m))
    (hΩ : ∀ z x, x+coordinatePeriodShift J (b-a) z∈Ω → x∈Ω)
    (k : Fin (m+1)) (hk : k∉J)
    (hface : ∀ y∈Icc (a∘k.succAbove) (b∘k.succAbove), k.insertNth (b k) y∉Ω)
    (u : PeriodicH10 a b Ω (coordinatePeriodSet J (b-a)))
    (A : CellCoordinates m→CellVectors m→L[ℝ] CellVectors m)
    (f : Lp ℝ 2 (volume.restrict (Icc a b)))
    (hweak : OAI.Analysis.PDE.Weak.WeakDivergenceEquation Ω
      (fun y ↦ A y (periodicRepresentative J a b u.val y)) (periodicRepresentative J a b f))
    (x : CellCoordinates m) (hx : x∈transverseInterior J a b) :
    ∃ (U : Set (CellCoordinates m)) (q : OAI.Analysis.PDE.Weak.H1Pair m)
      (F : Lp ℝ 2 (volume : Measure (CellCoordinates m))),
      IsOpen U ∧ x∈U ∧ q∈OAI.Analysis.PDE.Weak.H1Zero Ω ∧
      OAI.Analysis.PDE.Weak.WeakDivergenceEquation (Ω∩U) (fun y ↦ A y (q.2 y)) F ∧
      ∀ᵐ y ∂volume, y∈U →
        q.1 y=periodicRepresentative J a b (periodicValue a b Ω _ u) y ∧
        q.2 y=periodicRepresentative J a b u.val y ∧
        F y=periodicRepresentative J a b f y := by
  obtain ⟨c,d,hcd,hlen,ha,hb,hxc⟩ := exists_centered_periodic_cell J a b hab hL x hx
  have hface' := face_condition_shifted_cell J a b c d hab hL ha hb Ω hΩ k hk hface
  obtain ⟨η,U,hU,hxU,hsub,hη,hc,hs,hbounds,hone⟩ :=
    OAI.Analysis.PDE.Weak.exists_cutoff_with_open_plateau (isOpen_cellInterior c d) hxc
  have hM : ∀ y, |η y|≤1 := fun y ↦ by rw [abs_of_nonneg (hbounds y).1]; exact (hbounds y).2
  obtain ⟨K,hK⟩ := ((OAI.Analysis.PDE.Weak.hasCompactSupport_cellGradient hc).isCompact_range
    (continuous_cellGradient (hη.of_le (by simp)))).isBounded.exists_norm_le
  let v := periodicCellIsometry J a b c d hL hlen ha hb Ω u
  let p := periodicH1Pair c d Ω (coordinatePeriodSet J (b-a)) v
  let q := OAI.Analysis.PDE.Weak.cutoffH1Pair η (hη.of_le (by simp)) hM (fun y ↦ hK _ ⟨y,rfl⟩) p
  let F := cellZeroExtensionL2 c d (periodicCellPullback J a b c d hL hlen ha hb f)
  have hq : q∈OAI.Analysis.PDE.Weak.H1Zero Ω := cutoff_periodicH1Pair_mem_H1Zero_domain c d hcd Ω _ k hface' η hη hc
    (hs.trans (cellInterior_subset_Icc c d)) hM (fun y ↦ hK _ ⟨y,rfl⟩) v
  have hqe : ∀ᵐ y ∂volume, y∈U →
      q.1 y=periodicRepresentative J a b (periodicValue a b Ω _ u) y ∧
      q.2 y=periodicRepresentative J a b u.val y := by
    filter_upwards [cutoffH1Pair_eq_on U hU η (hη.of_le (by simp)) hM
      (fun y ↦ hK _ ⟨y,rfl⟩) hone p,
      periodicH1Pair_shifted_ae J a b c d hab hcd hL hlen ha hb Ω k hface hface' u] with y hy hz
    intro hyU
    exact ⟨(hy hyU).1.trans (hz (cellInterior_subset_Icc c d (hsub hyU))).1,
      (hy hyU).2.trans (hz (cellInterior_subset_Icc c d (hsub hyU))).2⟩
  have hFe : ∀ᵐ y ∂volume, y∈U → F y=periodicRepresentative J a b f y := by
    filter_upwards [periodicCellL2Extension_ae J a b c d hL hlen ha hb f] with y hy
    exact fun hyU ↦ hy (cellInterior_subset_Icc c d (hsub hyU))
  refine ⟨U,q,F,hU,hxU,hq,?_,?_⟩
  · apply weakEquation_congr_on hweak inter_subset_left
    · filter_upwards [hqe] with y hy
      exact fun hyU ↦ congrArg (A y) (hy hyU.2).2
    · filter_upwards [hFe] with y hy
      exact fun hyU ↦ hy hyU.2
  · filter_upwards [hqe,hFe] with y hy hz
    exact fun hyU ↦ ⟨(hy hyU).1,(hy hyU).2,hz hyU⟩

end OAI.Analysis.PDE.Variational
