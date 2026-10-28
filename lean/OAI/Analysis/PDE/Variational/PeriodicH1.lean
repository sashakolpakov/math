import OAI.Analysis.PDE.Variational.GlobalWeakSolution
import OAI.Analysis.PDE.Variational.LocalizedEquation
import OAI.Analysis.PDE.Weak.Elliptic.CutoffExistence

open Set Filter _root_.MeasureTheory
open scoped ContDiff Topology
noncomputable section
namespace OAI.Analysis.PDE.Variational

open OAI.Analysis.PDE.Weak

variable {m : ℕ}

theorem periodicH1Pair_shifted_ae
    (J : Finset (Fin (m+1))) (a b c d : CellCoordinates m)
    (hab : a≤b) (hcd : c≤d)
    (hL : ∀ i∈J, a i<b i) (hlen : d-c=b-a)
    (ha : ∀ i, i∉J → c i=a i) (hb : ∀ i, i∉J → d i=b i)
    (Ω : Set (CellCoordinates m)) (k : Fin (m+1))
    (hface : ∀ y∈Icc (a∘k.succAbove) (b∘k.succAbove), k.insertNth (b k) y∉Ω)
    (hface' : ∀ y∈Icc (c∘k.succAbove) (d∘k.succAbove), k.insertNth (d k) y∉Ω)
    (u : PeriodicH10 a b Ω (coordinatePeriodSet J (b-a))) :
    ∀ᵐ x ∂volume, x∈Icc c d →
      (periodicH1Pair c d Ω (coordinatePeriodSet J (b-a))
        (periodicCellIsometry J a b c d hL hlen ha hb Ω u)).1 x =
          periodicRepresentative J a b (periodicValue a b Ω _ u) x ∧
      (periodicH1Pair c d Ω (coordinatePeriodSet J (b-a))
        (periodicCellIsometry J a b c d hL hlen ha hb Ω u)).2 x =
          periodicRepresentative J a b u.val x := by
  have hv := periodicCellPullback_ae J a b c d hL hlen ha hb (periodicValue a b Ω _ u)
  have hg := periodicCellPullback_ae J a b c d hL hlen ha hb u.val
  rw [← periodicCellIsometry_value_pullback J a b c d hab hcd hL hlen ha hb Ω k hface hface' u] at hv
  rw [← periodicCellIsometry_gradient_pullback J a b c d hL hlen ha hb Ω u] at hg
  have hv' := (ae_restrict_iff' measurableSet_Icc).mp hv
  have hg' := (ae_restrict_iff' measurableSet_Icc).mp hg
  filter_upwards [hv', hg',
    periodicH1Pair_value_ae c d Ω _ (periodicCellIsometry J a b c d hL hlen ha hb Ω u),
    periodicH1Pair_gradient_ae c d Ω _ (periodicCellIsometry J a b c d hL hlen ha hb Ω u)]
      with x hx hy hz hw
  intro hxc
  simp only [hz, hw, cellZeroExtension, indicator_of_mem hxc]
  exact ⟨hx hxc, hy hxc⟩

/-- The explicit global periodic value and gradient are locally represented by
the genuine closure of smooth compactly supported H¹ graphs, including at
every seam of the original fundamental cell. -/
theorem periodicRepresentative_locally_H1
    (J : Finset (Fin (m+1))) (a b : CellCoordinates m) (hab : a≤b)
    (hL : ∀ i∈J, a i<b i) (Ω : Set (CellCoordinates m)) (hopen : IsOpen Ω)
    (htrans : Ω⊆transverseInterior J a b)
    (hΩ : ∀ z x, x+coordinatePeriodShift J (b-a) z∈Ω → x∈Ω)
    (k : Fin (m+1)) (hk : k∉J)
    (hface : ∀ y∈Icc (a∘k.succAbove) (b∘k.succAbove), k.insertNth (b k) y∉Ω)
    (u : PeriodicH10 a b Ω (coordinatePeriodSet J (b-a)))
    (x : CellCoordinates m) (hx : x∈Ω) :
    ∃ (U : Set (CellCoordinates m)) (q : OAI.Analysis.PDE.Weak.H1Pair m),
      IsOpen U ∧ x∈U ∧ U⊆Ω ∧ q∈OAI.Analysis.PDE.Weak.H1Zero univ ∧
      ∀ᵐ y ∂volume, y∈U →
        q.1 y=periodicRepresentative J a b (periodicValue a b Ω _ u) y ∧
        q.2 y=periodicRepresentative J a b u.val y := by
  obtain ⟨c,d,hcd,hlen,ha,hb,hxc⟩ := exists_centered_periodic_cell J a b hab hL x (htrans hx)
  have hface' := face_condition_shifted_cell J a b c d hab hL ha hb Ω hΩ k hk hface
  obtain ⟨η,U,hU,hxU,hsub,hη,hc,hs,hbounds,hone⟩ :=
    OAI.Analysis.PDE.Weak.exists_cutoff_with_open_plateau (hopen.inter (isOpen_cellInterior c d)) ⟨hx,hxc⟩
  have hM : ∀ y, |η y|≤1 := fun y ↦ by rw [abs_of_nonneg (hbounds y).1]; exact (hbounds y).2
  have hgcont := continuous_cellGradient (hη.of_le (by simp))
  obtain ⟨K,hK⟩ := ((OAI.Analysis.PDE.Weak.hasCompactSupport_cellGradient hc).isCompact_range hgcont).isBounded.exists_norm_le
  let v := periodicCellIsometry J a b c d hL hlen ha hb Ω u
  let p := periodicH1Pair c d Ω (coordinatePeriodSet J (b-a)) v
  let q := OAI.Analysis.PDE.Weak.cutoffH1Pair η (hη.of_le (by simp)) hM (fun y ↦ hK _ ⟨y,rfl⟩) p
  refine ⟨U,q,hU,hxU,hsub.trans inter_subset_left,?_,?_⟩
  · exact cutoff_periodicH1Pair_mem_H1Zero c d hcd Ω _ k hface' η hη hc
      (fun y hy ↦ cellInterior_subset_Icc c d (hs hy).2) hM (fun y ↦ hK _ ⟨y,rfl⟩)
      (subset_univ _) v
  · filter_upwards [cutoffH1Pair_eq_on U hU η (hη.of_le (by simp)) hM
      (fun y ↦ hK _ ⟨y,rfl⟩) hone p,
      periodicH1Pair_shifted_ae J a b c d hab hcd hL hlen ha hb Ω k hface hface' u]
        with y hy hz
    intro hyU
    exact ⟨(hy hyU).1.trans (hz (cellInterior_subset_Icc c d (hsub hyU).2)).1,
      (hy hyU).2.trans (hz (cellInterior_subset_Icc c d (hsub hyU).2)).2⟩

end OAI.Analysis.PDE.Variational
