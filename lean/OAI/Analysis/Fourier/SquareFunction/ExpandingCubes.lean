import OAI.Analysis.Fourier.SquareFunction.Dyadic.Root

/-! Cube geometry and exhaustion used to remove the root-average term. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set BoxIntegral Filter
open scoped ENNReal Topology

def IsCubeBox {ι : Type*} (I : Box ι) : Prop :=
  ∀ i j, I.upper i - I.lower i = I.upper j - I.lower j

theorem IsCubeBox.dyadicBox {ι : Type*} {I : Box ι} (hI : IsCubeBox I)
    (l : List (Set ι)) : IsCubeBox (dyadicBox I l) := by
  intro i j
  rw [dyadicBox_edge, dyadicBox_edge, hI i j]

def expandingCube (ι : Type*) (N : ℕ) : Box ι where
  lower := fun _ => -((N : ℝ) + 1)
  upper := fun _ => (N : ℝ) + 1
  lower_lt_upper := fun _ => by linarith [Nat.cast_nonneg (α := ℝ) N]

theorem expandingCube_isCube (ι : Type*) (N : ℕ) : IsCubeBox (expandingCube ι N) :=
  fun _ _ => rfl

theorem expandingCube_mono (ι : Type*) : Monotone (fun N => (expandingCube ι N : Set (ι → ℝ))) := by
  intro N M hNM x hx i
  have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hi := hx i
  change -((N : ℝ) + 1) < x i ∧ x i ≤ (N : ℝ) + 1 at hi
  change -((M : ℝ) + 1) < x i ∧ x i ≤ (M : ℝ) + 1
  constructor <;> linarith [hi.1, hi.2]

theorem iUnion_expandingCube (ι : Type*) [Fintype ι] :
    (⋃ N, (expandingCube ι N : Set (ι → ℝ))) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  apply mem_iUnion.mpr
  refine ⟨N, ?_⟩
  intro i
  have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  change -((N : ℝ) + 1) < x i ∧ x i ≤ (N : ℝ) + 1
  constructor <;> linarith [neg_abs_le (x i), le_abs_self (x i)]

theorem volume_univ_pi_real (ι : Type*) [Fintype ι] [Nonempty ι] :
    volume (univ : Set (ι → ℝ)) = ∞ := by
  simp [volume_pi]

theorem tendsto_volume_expandingCube (ι : Type*) [Fintype ι] [Nonempty ι] :
    Tendsto (fun N => volume (expandingCube ι N : Set (ι → ℝ))) atTop (𝓝 ∞) := by
  simpa only [Function.comp_def, iUnion_expandingCube, volume_univ_pi_real] using
    (tendsto_measure_iUnion_atTop (μ := volume) (expandingCube_mono ι))

theorem tendsto_volume_expandingCube_rpow (ι : Type*) [Fintype ι] [Nonempty ι]
    {p : ℝ} (hp : 1 < p) :
    Tendsto (fun N => volume (expandingCube ι N : Set (ι → ℝ)) ^ (1 - p)) atTop (𝓝 0) := by
  simpa only [ENNReal.top_rpow_of_neg (sub_neg.mpr hp)] using
    (tendsto_volume_expandingCube ι).ennrpow_const (1 - p)

end OAI.Analysis.Fourier.SquareFunction
