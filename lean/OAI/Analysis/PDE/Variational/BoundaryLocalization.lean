import OAI.Analysis.PDE.Variational.CutoffSupport
import OAI.Analysis.PDE.Variational.BoundaryH1

open Set _root_.MeasureTheory Filter
open scoped ContDiff Topology
noncomputable section
namespace OAI.Analysis.PDE.Variational

open OAI.Analysis.PDE.Weak

variable {m : ℕ}

/-- A boundary-chart-ready localization of the actual periodic weak
solution. Both the zero-trace H¹ graph and the full-domain equation with
an L² load are supplied, with compact support in any prescribed patch. -/
theorem periodicRepresentative_boundary_localization
    (J : Finset (Fin (m+1))) (a b : CellCoordinates m) (hab : a≤b)
    (hL : ∀ i∈J, a i<b i) (Ω : Set (CellCoordinates m))
    (hΩ : ∀ z x, x+coordinatePeriodShift J (b-a) z∈Ω → x∈Ω)
    (k : Fin (m+1)) (hk : k∉J)
    (hface : ∀ y∈Icc (a∘k.succAbove) (b∘k.succAbove), k.insertNth (b k) y∉Ω)
    (u : PeriodicH10 a b Ω (coordinatePeriodSet J (b-a)))
    (A : CellCoordinates m→CellVectors m→L[ℝ] CellVectors m)
    (hA : ContDiff ℝ 1 A) {M : ℝ} (hAM : ∀ y, ‖A y‖≤M)
    (f : Lp ℝ 2 (volume.restrict (Icc a b)))
    (hweak : OAI.Analysis.PDE.Weak.WeakDivergenceEquation Ω
      (fun y ↦ A y (periodicRepresentative J a b u.val y)) (periodicRepresentative J a b f))
    (x : CellCoordinates m) (hx : x∈transverseInterior J a b)
    {W : Set (CellCoordinates m)} (hW : IsOpen W) (hxW : x∈W) :
    ∃ (U K : Set (CellCoordinates m)) (q : OAI.Analysis.PDE.Weak.H1Pair m)
      (F : Lp ℝ 2 (volume : Measure (CellCoordinates m))),
      IsOpen U ∧ x∈U ∧ U⊆W ∧ IsCompact K ∧ K⊆W ∧ q∈OAI.Analysis.PDE.Weak.H1Zero (Ω∩W) ∧
      OAI.Analysis.PDE.Weak.WeakDivergenceEquation Ω (fun y ↦ A y (q.2 y)) F ∧
      (∀ᵐ y ∂volume, y∉K → q.1 y=0 ∧ q.2 y=0 ∧ F y=0) ∧
      (∀ᵐ y ∂volume, y∈U →
        q.1 y=periodicRepresentative J a b (periodicValue a b Ω _ u) y ∧
        q.2 y=periodicRepresentative J a b u.val y ∧
        F y=periodicRepresentative J a b f y) := by
  obtain ⟨V,p,g,hV,hxV,hp,he,hagree⟩ :=
    periodicRepresentative_boundary_H1_equation J a b hab hL Ω hΩ k hk hface u A f hweak x hx
  obtain ⟨η,U,hU,hxU,hsub,hη,hs,hsW,hbound,hone⟩ :=
    OAI.Analysis.PDE.Weak.exists_cutoff_with_open_plateau (hW.inter hV) ⟨hxW,hxV⟩
  have hN : ∀ y, |η y|≤1 := fun y ↦ by rw [abs_of_nonneg (hbound y).1]; exact (hbound y).2
  obtain ⟨C,hC⟩ := ((OAI.Analysis.PDE.Weak.hasCompactSupport_cellGradient hs).isCompact_range
    (continuous_cellGradient (hη.of_le (by simp)))).isBounded.exists_norm_le
  have hC' : ∀ y, ‖cellGradient η y‖≤C := fun y ↦ hC _ (mem_range_self y)
  let q := OAI.Analysis.PDE.Weak.cutoffH1Pair η (hη.of_le (by simp)) hN hC' p
  obtain ⟨_,F,hqeq,hF,hzero⟩ := cutoffDirichlet_equation_L2_supported p hp A hA hAM g he
    η hη hs (hsW.trans inter_subset_right) hN hC'
  have hq : q∈OAI.Analysis.PDE.Weak.H1Zero (Ω∩W) :=
    OAI.Analysis.PDE.Weak.H1Zero.cutoff hp η hη hN hC' (fun y hy ↦ ⟨hy.2,(hsW hy.1).1⟩)
  refine ⟨U,tsupport η,q,F,hU,hxU,hsub.trans inter_subset_left,hs,
    hsW.trans inter_subset_left,hq,hqeq,hzero,?_⟩
  filter_upwards [hagree,hF,cutoffH1Pair_eq_on U hU η (hη.of_le (by simp)) hN hC' hone p]
    with y hy hFy hqy
  intro hyU
  have hyV := (hsub hyU).2
  exact ⟨(hqy hyU).1.trans (hy hyV).1,
    (hqy hyU).2.trans (hy hyV).2.1,
    hFy.trans ((cutoffDirichletLoad_eq_on A η p g hU hone hyU).trans (hy hyV).2.2)⟩

end OAI.Analysis.PDE.Variational
