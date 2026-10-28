import OAI.Analysis.PDE.Variational.Periodization
import OAI.Analysis.PDE.Variational.ZeroExtension

open Set Filter
open scoped ContDiff Topology
noncomputable section

namespace OAI.Analysis.PDE.Variational

variable {m : ℕ}

def coordinatePeriodShift (J : Finset (Fin (m+1))) (L : CellCoordinates m) :
    (J → ℤ) →+ CellCoordinates m where
  toFun z i := if hi : i ∈ J then (z ⟨i,hi⟩ : ℝ) * L i else 0
  map_zero' := by ext i; simp
  map_add' z w := by
    ext i
    by_cases hi : i∈J <;> simp [hi, add_mul]

@[simp] theorem coordinatePeriodShift_apply (J : Finset (Fin (m+1)))
    (L : CellCoordinates m) (z : J → ℤ) (i : J) :
    coordinatePeriodShift J L z i = (z i : ℝ) * L i := by
  simp [coordinatePeriodShift, i.property]

theorem finite_coordinatePeriodShift_norm (J : Finset (Fin (m+1)))
    (L : CellCoordinates m) (hL : ∀ i∈J, 0<L i) (R : ℝ) :
    {z : J → ℤ | ‖coordinatePeriodShift J L z‖ ≤ R}.Finite := by
  let N : J → ℤ := fun i ↦ ⌈R / L i⌉
  have hf : (Set.Icc (fun i : J ↦ -(N i)) N).Finite := Set.finite_Icc _ _
  apply hf.subset
  intro z hz
  have hboth (i : J) : -(N i) ≤ z i ∧ z i ≤ N i := by
    have hn := (norm_le_pi_norm (coordinatePeriodShift J L z) i.val).trans hz
    rw [coordinatePeriodShift_apply, Real.norm_eq_abs, abs_mul,
      abs_of_pos (hL i i.property)] at hn
    have hdiv : |(z i : ℝ)| ≤ R / L i := (le_div_iff₀ (hL i i.property)).mpr hn
    have hceil : R / L i ≤ (N i : ℝ) := Int.le_ceil _
    have hu : (z i : ℝ) ≤ (N i : ℝ) := (le_abs_self _).trans (hdiv.trans hceil)
    have hl : (-(N i) : ℝ) ≤ (z i : ℝ) := by
      have := neg_le_abs (z i : ℝ)
      linarith
    constructor
    · exact_mod_cast hl
    · exact_mod_cast hu
  exact ⟨fun i ↦ (hboth i).1, fun i ↦ (hboth i).2⟩

def coordinatePeriodSet (J : Finset (Fin (m+1))) (L : CellCoordinates m) :
    Set (CellCoordinates m) := Set.range (coordinatePeriodShift J L)

theorem coordinate_translate_off_cell (J : Finset (Fin (m+1)))
    (a b : CellCoordinates m) (hL : ∀ i∈J, a i<b i)
    {φ : CellCoordinates m → ℝ} (hs : tsupport φ ⊆ cellInterior a b)
    {x : CellCoordinates m} (hx : x∈Icc a b) (z : J → ℤ) (hz : z≠0) :
    φ (x + coordinatePeriodShift J (b-a) z) = 0 := by
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, z i≠0 := by
    by_contra h
    apply hz
    ext i
    simpa using not_exists.mp h i
  have hy := hs (subset_tsupport _ hne) i
  simp only [Pi.add_apply, coordinatePeriodShift_apply, Pi.sub_apply] at hy
  have hai := hx.1 i
  have hbi := hx.2 i
  have hlen := hL i i.property
  rcases (show z i ≤ -1 ∨ 1 ≤ z i by omega) with hneg | hpos
  · have hzR : (z i : ℝ) ≤ -1 := by exact_mod_cast hneg
    nlinarith [mul_le_mul_of_nonneg_right hzR (sub_nonneg.mpr hlen.le)]
  · have hzR : (1 : ℝ) ≤ (z i : ℝ) := by exact_mod_cast hpos
    nlinarith [mul_le_mul_of_nonneg_right hzR (sub_nonneg.mpr hlen.le)]

theorem coordinatePeriodization_eq (J : Finset (Fin (m+1)))
    (a b : CellCoordinates m) (hL : ∀ i∈J, a i<b i)
    {φ : CellCoordinates m → ℝ} (hs : tsupport φ ⊆ cellInterior a b)
    {x : CellCoordinates m} (hx : x∈Icc a b) :
    discretePeriodization (coordinatePeriodShift J (b-a)) φ x = φ x :=
  discretePeriodization_eq_self _ _ _ (coordinate_translate_off_cell J a b hL hs hx)

end OAI.Analysis.PDE.Variational
