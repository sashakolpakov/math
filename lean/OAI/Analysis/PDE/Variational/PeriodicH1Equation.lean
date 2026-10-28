import OAI.Analysis.PDE.Variational.PeriodicH1

open Set Filter _root_.MeasureTheory
noncomputable section
namespace OAI.Analysis.PDE.Variational

open OAI.Analysis.PDE.Weak

variable {m : ℕ}

theorem periodicCellL2Extension_ae {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (J : Finset (Fin (m+1))) (a b c d : CellCoordinates m)
    (hL : ∀ i∈J, a i<b i) (hlen : d-c=b-a)
    (ha : ∀ i, i∉J → c i=a i) (hb : ∀ i, i∉J → d i=b i)
    (f : Lp H 2 (volume.restrict (Icc a b))) :
    ∀ᵐ x ∂volume, x∈Icc c d →
      cellZeroExtensionL2 c d (periodicCellPullback J a b c d hL hlen ha hb f) x =
        periodicRepresentative J a b f x := by
  have h := (ae_restrict_iff' measurableSet_Icc).mp
    (periodicCellPullback_ae J a b c d hL hlen ha hb f)
  filter_upwards [h, cellZeroExtensionL2_ae c d
    (periodicCellPullback J a b c d hL hlen ha hb f)] with x hx hy
  intro hxc
  simpa only [hy, cellZeroExtension, indicator_of_mem hxc] using hx hxc

/-- Every periodic variational weak solution has, near each point, an actual
global H¹ graph representative solving the same equation with a global L² load.
The representatives are identified with the periodic value and gradient. -/
theorem periodicRepresentative_local_H1_equation
    (J : Finset (Fin (m+1))) (a b : CellCoordinates m) (hab : a≤b)
    (hL : ∀ i∈J, a i<b i) (Ω : Set (CellCoordinates m)) (hopen : IsOpen Ω)
    (htrans : Ω⊆transverseInterior J a b)
    (hΩ : ∀ z x, x+coordinatePeriodShift J (b-a) z∈Ω → x∈Ω)
    (k : Fin (m+1)) (hk : k∉J)
    (hface : ∀ y∈Icc (a∘k.succAbove) (b∘k.succAbove), k.insertNth (b k) y∉Ω)
    (u : PeriodicH10 a b Ω (coordinatePeriodSet J (b-a)))
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (f : Lp ℝ 2 (volume.restrict (Icc a b)))
    (hweak : OAI.Analysis.PDE.Weak.WeakDivergenceEquation Ω
      (fun y ↦ A y (periodicRepresentative J a b u.val y))
      (periodicRepresentative J a b f))
    (x : CellCoordinates m) (hx : x∈Ω) :
    ∃ (U : Set (CellCoordinates m)) (q : OAI.Analysis.PDE.Weak.H1Pair m)
      (F : Lp ℝ 2 (volume : Measure (CellCoordinates m))),
      IsOpen U ∧ x∈U ∧ U⊆Ω ∧ q∈OAI.Analysis.PDE.Weak.H1Zero univ ∧
      OAI.Analysis.PDE.Weak.WeakDivergenceEquation U (fun y ↦ A y (q.2 y)) F ∧
      ∀ᵐ y ∂volume, y∈U →
        q.1 y=periodicRepresentative J a b (periodicValue a b Ω _ u) y ∧
        q.2 y=periodicRepresentative J a b u.val y ∧
        F y=periodicRepresentative J a b f y := by
  obtain ⟨V,q,hV,hxV,hVΩ,hq,hqe⟩ := periodicRepresentative_locally_H1
    J a b hab hL Ω hopen htrans hΩ k hk hface u x hx
  obtain ⟨c,d,_,hlen,ha,hb,hxc⟩ := exists_centered_periodic_cell J a b hab hL x (htrans hx)
  let F := cellZeroExtensionL2 c d (periodicCellPullback J a b c d hL hlen ha hb f)
  have hFe : ∀ᵐ y ∂volume, y∈Icc c d → F y=periodicRepresentative J a b f y :=
    periodicCellL2Extension_ae J a b c d hL hlen ha hb f
  refine ⟨V∩cellInterior c d,q,F,hV.inter (isOpen_cellInterior c d),⟨hxV,hxc⟩,
    inter_subset_left.trans hVΩ,hq,?_,?_⟩
  · apply weakEquation_congr_on hweak (inter_subset_left.trans hVΩ)
    · filter_upwards [hqe] with y hy
      intro hyU
      rw [(hy hyU.1).2]
    · filter_upwards [hFe] with y hy
      intro hyU
      exact hy (cellInterior_subset_Icc c d hyU.2)
  · filter_upwards [hqe,hFe] with y hy hz
    intro hyU
    exact ⟨(hy hyU.1).1,(hy hyU.1).2,hz (cellInterior_subset_Icc c d hyU.2)⟩

end OAI.Analysis.PDE.Variational
