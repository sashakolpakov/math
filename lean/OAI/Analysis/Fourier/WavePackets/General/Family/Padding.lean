import OAI.Analysis.Fourier.WavePackets.General.Family.Solution
import OAI.Analysis.Fourier.WavePackets.Dirichlet.Padding

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open scoped Topology ContDiff

variable {Z P V ι : Type*} {m : ℕ}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
local notation "E₃" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 3
local notation "E₄" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4

def familyDropFourth (p : Z × E₄) : Z × E₃ := (p.1,dropFourth m p.2)

def familyPadFourth (Φ : Z × E₃ → E₃) (p : Z × E₄) : E₄ :=
  insertFourth m (Φ (familyDropFourth p)) + fourthInjection m (fourthCoordinates m p.2)

theorem contDiff_familyDropFourth : ContDiff ℝ ∞ (familyDropFourth (Z := Z) (m := m)) :=
  contDiff_fst.prodMk ((dropFourth m).contDiff.comp contDiff_snd)

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
@[simp] theorem dropFourth_familyPadFourth (Φ : Z × E₃ → E₃) (p : Z × E₄) :
    dropFourth m (familyPadFourth Φ p) = Φ (familyDropFourth p) := by
  simp only [familyPadFourth, map_add, dropFourth_insertFourth,
    dropFourth_fourthInjection, add_zero]

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
@[simp] theorem fourthCoordinates_familyPadFourth (Φ : Z × E₃ → E₃) (p : Z × E₄) :
    fourthCoordinates m (familyPadFourth Φ p) = fourthCoordinates m p.2 := by
  simp only [familyPadFourth, map_add, fourthCoordinates_insertFourth,
    fourthCoordinates_fourthInjection, zero_add]

theorem contDiffOn_familyPadFourth {Φ : Z × E₃ → E₃} {S : Set (Z × E₃)}
    (hΦ : ContDiffOn ℝ ∞ Φ S) :
    ContDiffOn ℝ ∞ (familyPadFourth Φ) (familyDropFourth ⁻¹' S) := by
  have h := hΦ.comp contDiff_familyDropFourth.contDiffOn (fun _ hp => hp)
  exact ((insertFourth m).contDiff.comp_contDiffOn h).add
    (((fourthInjection m).contDiff.comp
      ((fourthCoordinates m).contDiff.comp contDiff_snd)).contDiffOn)

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
theorem familyPadFourth_eq_add_defect (Φ : Z × E₃ → E₃) (z : Z) (x : E₄) :
    familyPadFourth Φ (z,x) =
      x + insertFourth m (Φ (z,dropFourth m x) - dropFourth m x) := by
  simp only [familyPadFourth, familyDropFourth, map_sub]
  calc
    _ = (insertFourth m (dropFourth m x) + fourthInjection m (fourthCoordinates m x)) +
        (insertFourth m (Φ (z,dropFourth m x)) - insertFourth m (dropFourth m x)) := by abel
    _ = _ := by rw [insertFourth_dropFourth_add]

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [Fintype ι] in
theorem familyDisplacement_periodic {Φ : Z × E₃ → E₃}
    (hΦ : ∀ z (l : Submodule.span ℤ (range b)) x,
      Φ (z,x + e.symm ((l:P),0)) = Φ (z,x) + e.symm ((l:P),0)) (z : Z) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun y => Φ (z,y) - y) := by
  intro y k
  rw [OAI.Analysis.PDE.Dirichlet.lattice_translate_eq, add_comm (e.symm ((k:P),0)) y]
  change Φ (z,y + e.symm ((k:P),0)) - (y + e.symm ((k:P),0)) = Φ (z,y) - y
  rw [hΦ]
  abel

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [Fintype ι] in
theorem paddedFamilyDisplacement_periodic {Φ : Z × E₃ → E₃}
    (hΦ : ∀ z (l : Submodule.span ℤ (range b)) x,
      Φ (z,x + e.symm ((l:P),0)) = Φ (z,x) + e.symm ((l:P),0)) (z : Z) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic (P := P × (Fin m → ℝ)) (V := V) (ι := ι ⊕ Fin m)
      (paddedLatticeSplit (m := m) (P := P) (V := V) e) (paddedLatticeBasis (m := m) b)
      (fun x : E₄ => Φ (z,dropFourth m x) - dropFourth m x) :=
  latticePeriodic_dropFourth (W := E₃) (m := m) (P := P) (V := V) (ι := ι)
    e b (familyDisplacement_periodic hΦ z)

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [Fintype ι] in
theorem familyPadFourth_periodic {Φ : Z × E₃ → E₃}
    (hΦ : ∀ z (l : Submodule.span ℤ (range b)) x,
      Φ (z,x + e.symm ((l:P),0)) = Φ (z,x) + e.symm ((l:P),0))
    (z : Z) (l : Submodule.span ℤ (range (paddedLatticeBasis (m := m) b))) (x : E₄) :
    familyPadFourth Φ (z,x + (paddedLatticeSplit e).symm ((l : P × (Fin m → ℝ)),0)) =
      familyPadFourth Φ (z,x) + (paddedLatticeSplit e).symm ((l : P × (Fin m → ℝ)),0) := by
  have hp := paddedFamilyDisplacement_periodic hΦ z
  have hh := OAI.Analysis.PDE.Dirichlet.latticePeriodic_add_shift (P := P × (Fin m → ℝ)) (V := V) (ι := ι ⊕ Fin m)
    (paddedLatticeSplit (m := m) (P := P) (V := V) e)
    (paddedLatticeBasis (m := m) b) hp x l
  change Φ (z,dropFourth m (x + (paddedLatticeSplit e).symm ((l : P × (Fin m → ℝ)),0))) -
      dropFourth m (x + (paddedLatticeSplit e).symm ((l : P × (Fin m → ℝ)),0)) =
    Φ (z,dropFourth m x) - dropFourth m x at hh
  rw [familyPadFourth_eq_add_defect, familyPadFourth_eq_add_defect, hh]
  exact add_right_comm _ _ _

variable {D : Z → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.threeSlots e b} {z₀ : Z} {U : Set Z}

/-- Pad a genuine smooth family by periodic fourth coordinates, leaving all
physical domains and all original coefficients unchanged. -/
def LocalDirichletFamily.padFourth (G : LocalDirichletFamily D z₀ U) :
    LocalDirichletFamily (fun z => (D z).padFourth) z₀ U where
  open_parameter := G.open_parameter
  base_mem := G.base_mem
  forward := familyPadFourth G.forward
  backward := familyPadFourth G.backward
  sourceNeighborhood := familyDropFourth ⁻¹' G.sourceNeighborhood
  targetNeighborhood := familyDropFourth ⁻¹' G.targetNeighborhood
  source_open := G.source_open.preimage contDiff_familyDropFourth.continuous
  target_open := G.target_open.preimage contDiff_familyDropFourth.continuous
  source_parameter p hp := G.source_parameter hp
  target_parameter p hp := G.target_parameter hp
  source_closed p hp := G.source_closed hp
  target_closed p hp := G.target_closed hp
  forward_smooth := contDiffOn_familyPadFourth G.forward_smooth
  backward_smooth := contDiffOn_familyPadFourth G.backward_smooth
  defining_smooth := G.defining_smooth.comp contDiff_familyDropFourth.contDiffOn (fun _ hp => hp)
  background_smooth := G.background_smooth.comp contDiff_familyDropFourth.contDiffOn (fun _ hp => hp)
  density_smooth := G.density_smooth.comp contDiff_familyDropFourth.contDiffOn (fun _ hp => hp)
  forward_mem p hp := by
    change familyDropFourth (p.1,familyPadFourth G.forward p) ∈ G.targetNeighborhood
    simpa only [familyDropFourth, dropFourth_familyPadFourth] using G.forward_mem _ hp
  backward_mem p hp := by
    change familyDropFourth (p.1,familyPadFourth G.backward p) ∈ G.sourceNeighborhood
    simpa only [familyDropFourth, dropFourth_familyPadFourth] using G.backward_mem _ hp
  backward_forward p hp := by
    apply (fourthSplit m).injective
    apply Prod.ext
    · change dropFourth m (familyPadFourth G.backward (p.1,familyPadFourth G.forward p)) =
        dropFourth m p.2
      simpa only [dropFourth_familyPadFourth, familyDropFourth] using G.backward_forward _ hp
    · change fourthCoordinates m (familyPadFourth G.backward (p.1,familyPadFourth G.forward p)) =
        fourthCoordinates m p.2
      simp only [fourthCoordinates_familyPadFourth]
  forward_backward p hp := by
    apply (fourthSplit m).injective
    apply Prod.ext
    · change dropFourth m (familyPadFourth G.forward (p.1,familyPadFourth G.backward p)) =
        dropFourth m p.2
      simpa only [dropFourth_familyPadFourth, familyDropFourth] using G.forward_backward _ hp
    · change fourthCoordinates m (familyPadFourth G.forward (p.1,familyPadFourth G.backward p)) =
        fourthCoordinates m p.2
      simp only [fourthCoordinates_familyPadFourth]
  forward_base x hx := by
    rw [familyPadFourth, familyDropFourth, G.forward_base _ hx]
    exact insertFourth_dropFourth_add m x
  backward_base x hx := by
    rw [familyPadFourth, familyDropFourth, G.backward_base _ hx]
    exact insertFourth_dropFourth_add m x
  forward_strict z hz x hx := by
    change (D z).defining (dropFourth m (familyPadFourth G.forward (z,x))) < 0
    rw [dropFourth_familyPadFourth]
    exact G.forward_strict z hz _ hx
  backward_strict z hz x hx := by
    change (D z₀).defining (dropFourth m (familyPadFourth G.backward (z,x))) < 0
    rw [dropFourth_familyPadFourth]
    exact G.backward_strict z hz _ hx
  forward_closed z hz x hx := by
    change (D z).defining (dropFourth m (familyPadFourth G.forward (z,x))) ≤ 0
    rw [dropFourth_familyPadFourth]
    exact G.forward_closed z hz _ hx
  backward_closed z hz x hx := by
    change (D z₀).defining (dropFourth m (familyPadFourth G.backward (z,x))) ≤ 0
    rw [dropFourth_familyPadFourth]
    exact G.backward_closed z hz _ hx
  forward_periodic := familyPadFourth_periodic G.forward_periodic
  backward_periodic := familyPadFourth_periodic G.backward_periodic
  backward_first z hz x := by
    simp only [paddedLatticeSplit_apply, dropFourth_familyPadFourth,
      fourthCoordinates_familyPadFourth, familyDropFourth, G.backward_first z hz]
  defining_transverse z p v := by
    change (D z).defining (dropFourth m ((paddedLatticeSplit e).symm (p,v))) =
      (D z).defining (dropFourth m ((paddedLatticeSplit e).symm (0,v)))
    rcases p with ⟨p,d⟩
    rw [show (0 : P × (Fin m → ℝ)) = (0,0) from rfl]
    simp only [paddedLatticeSplit_symm, map_add, dropFourth_insertFourth,
      dropFourth_fourthInjection, add_zero]
    exact G.defining_transverse z p v

theorem LocallyTrivialDirichletData.padFourth {A : Set Z}
    (hD : LocallyTrivialDirichletData D A) :
    LocallyTrivialDirichletData (fun z => (D z).padFourth) A := by
  refine ⟨hD.1,?_⟩
  intro z hz
  obtain ⟨U,hU,⟨G⟩⟩ := hD.2 z hz
  exact ⟨U,hU,⟨G.padFourth⟩⟩

end OAI.Analysis.Fourier.WavePackets
