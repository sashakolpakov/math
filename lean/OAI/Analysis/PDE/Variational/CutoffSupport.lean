import OAI.Analysis.PDE.Variational.CutoffLoad

open Set _root_.MeasureTheory Filter
open scoped ContDiff Topology
noncomputable section
namespace OAI.Analysis.PDE.Variational

open OAI.Analysis.PDE.Weak

variable {m : ℕ}

theorem cellDivergence_zero_on_open {B : CellCoordinates m → CellVectors m}
    {U : Set (CellCoordinates m)} (hU : IsOpen U) (hB : ∀ x∈U, B x=0)
    {x : CellCoordinates m} (hx : x∈U) : cellDivergence B x=0 := by
  apply Finset.sum_eq_zero
  intro j _
  have heq : (fun y ↦ B y j) =ᶠ[𝓝 x] (fun _ ↦ (0:ℝ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    simp [hB y hy]
  rw [heq.fderiv_eq]
  simp

theorem cutoffDirichletLoad_eq_on
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (η : CellCoordinates m → ℝ) (p : OAI.Analysis.PDE.Weak.H1Pair m) (f : CellCoordinates m → ℝ)
    {U : Set (CellCoordinates m)} (hU : IsOpen U) (hone : ∀ x∈U, η x=1)
    {x : CellCoordinates m} (hx : x∈U) : cutoffDirichletLoad A η p f x=f x := by
  have hg := cellGradient_eq_zero_of_eq_one hU hone hx
  have hdiv : cellDivergence (fun y ↦ A y (cellGradient η y)) x=0 :=
    cellDivergence_zero_on_open hU (fun y hy ↦ by rw [cellGradient_eq_zero_of_eq_one hU hone hy,map_zero]) hx
  simp [cutoffDirichletLoad,hone x hx,hg,hdiv]

theorem tsupport_cellDivergence_subset (B : CellCoordinates m → CellVectors m) :
    tsupport (cellDivergence B)⊆tsupport B := by
  apply closure_minimal _ (isClosed_tsupport B)
  intro x hx
  by_contra hnot
  apply hx
  change ∑ j, fderiv ℝ (fun y ↦ B y j) x (Pi.single j 1)=0
  apply Finset.sum_eq_zero
  intro j _
  have hj : tsupport (fun y ↦ B y j)⊆tsupport B := by
    apply closure_minimal _ (isClosed_tsupport B)
    intro y hy
    apply subset_tsupport B
    intro hzero
    apply hy
    simp [hzero]
  rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hnot (hj h))]
  rfl

theorem tsupport_gradient_subset (η : CellCoordinates m → ℝ) :
    tsupport (cellGradient η)⊆tsupport η := by
  apply closure_minimal _ (isClosed_tsupport η)
  intro x hx
  by_contra hnot
  exact hx (cellGradient_zero_off_tsupport hnot)

theorem cutoffDirichletLoad_zero_off
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (η : CellCoordinates m → ℝ) (p : OAI.Analysis.PDE.Weak.H1Pair m) (f : CellCoordinates m → ℝ)
    {x : CellCoordinates m} (hx : x∉tsupport η) :
    cutoffDirichletLoad A η p f x=0 := by
  have hB : tsupport (fun y ↦ A y (cellGradient η y))⊆tsupport η :=
    (OAI.Analysis.PDE.Weak.tsupport_operator_apply_subset A (cellGradient η)).trans (tsupport_gradient_subset η)
  have hdiv : cellDivergence (fun y ↦ A y (cellGradient η y)) x=0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hB (tsupport_cellDivergence_subset _ h)))
  simp [cutoffDirichletLoad,image_eq_zero_of_notMem_tsupport hx,
    cellGradient_zero_off_tsupport hx,hdiv]

theorem cutoffH1Pair_zero_off
    (η : CellCoordinates m → ℝ) (hη : ContDiff ℝ 1 η)
    {N K : ℝ} (hN : ∀ x, |η x|≤N) (hK : ∀ x, ‖cellGradient η x‖≤K)
    (p : OAI.Analysis.PDE.Weak.H1Pair m) :
    ∀ᵐ x ∂volume, x∉tsupport η →
      (OAI.Analysis.PDE.Weak.cutoffH1Pair η hη hN hK p).1 x=0 ∧
      (OAI.Analysis.PDE.Weak.cutoffH1Pair η hη hN hK p).2 x=0 := by
  filter_upwards [OAI.Analysis.PDE.Weak.cutoffH1Pair_value_ae η hη hN hK p,
    OAI.Analysis.PDE.Weak.cutoffH1Pair_gradient_ae η hη hN hK p] with x hv hg
  intro hx
  simp [hv,hg,image_eq_zero_of_notMem_tsupport hx,cellGradient_zero_off_tsupport hx]

/-- The localized equation and its L² load are genuinely confined to the
chosen physical patch, including the zero-trace graph membership there. -/
theorem cutoffDirichlet_equation_L2_supported
    {Ω V : Set (CellCoordinates m)} (p : OAI.Analysis.PDE.Weak.H1Pair m) (hp : p∈OAI.Analysis.PDE.Weak.H1Zero Ω)
    (A : CellCoordinates m → CellVectors m →L[ℝ] CellVectors m)
    (hA : ContDiff ℝ 1 A) {M : ℝ} (hAM : ∀ x, ‖A x‖≤M)
    (f : Lp ℝ 2 (volume : Measure (CellCoordinates m)))
    (hweak : OAI.Analysis.PDE.Weak.WeakDivergenceEquation (Ω∩V) (fun x ↦ A x (p.2 x)) f)
    (η : CellCoordinates m → ℝ) (hη : ContDiff ℝ ∞ η)
    (hs : HasCompactSupport η) (hV : tsupport η⊆V)
    {N K : ℝ} (hN : ∀ x, |η x|≤N) (hK : ∀ x, ‖cellGradient η x‖≤K) :
    let q := OAI.Analysis.PDE.Weak.cutoffH1Pair η (hη.of_le (by simp)) hN hK p
    q∈OAI.Analysis.PDE.Weak.H1Zero (Ω∩V) ∧ ∃ F : Lp ℝ 2 (volume : Measure (CellCoordinates m)),
      OAI.Analysis.PDE.Weak.WeakDivergenceEquation Ω (fun x ↦ A x (q.2 x)) F ∧
      F =ᵐ[volume] cutoffDirichletLoad A η p f ∧
      ∀ᵐ x ∂volume, x∉tsupport η → q.1 x=0 ∧ q.2 x=0 ∧ F x=0 := by
  dsimp only
  obtain ⟨_,F,hF,he⟩ := cutoffDirichlet_equation_L2 p hp A hA hAM f hweak η hη hs hV hN hK
  refine ⟨OAI.Analysis.PDE.Weak.H1Zero.cutoff hp η hη hN hK (fun x hx ↦ ⟨hx.2,hV hx.1⟩),F,he,hF,?_⟩
  filter_upwards [hF,cutoffH1Pair_zero_off η (hη.of_le (by simp)) hN hK p] with x hx hq
  intro hxs
  exact ⟨(hq hxs).1,(hq hxs).2,hx.trans (cutoffDirichletLoad_zero_off A η p f hxs)⟩

end OAI.Analysis.PDE.Variational
