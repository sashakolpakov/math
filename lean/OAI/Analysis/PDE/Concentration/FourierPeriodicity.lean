import OAI.Analysis.PDE.Concentration.Packet.Phase
import OAI.Analysis.PDE.Concentration.Lattice.Unwrap

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current

theorem planeWave_periodic_integer {d : ℕ} (ξ w : OAI.Analysis.Calculus.Current.SpatialSpace d) (k : ℤ)
    (hw : inner ℝ w ξ = (k : ℝ)) (x : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    planeWave ξ (x + w) = planeWave ξ x := by
  have he : Complex.exp (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I k using 1 ; push_cast ; ring_nf
  unfold planeWave
  rw [inner_add_left, hw, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add, he, mul_one]

theorem finiteWave_periodic_integer {d : ℕ} {ι : Type*} [Fintype ι]
    (ξ : ι → OAI.Analysis.Calculus.Current.SpatialSpace d) (a : ι → ℂ) (w : OAI.Analysis.Calculus.Current.SpatialSpace d)
    (hw : ∀ i, ∃ k : ℤ, inner ℝ w (ξ i) = (k : ℝ)) (x : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    finiteWave ξ a (x + w) = finiteWave ξ a x := by
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨k, hk⟩ := hw i
  rw [planeWave_periodic_integer (ξ i) w k hk]

theorem latticeIntegerVector_eq_sum {d : ℕ} (k : Option (Fin d) → ℤ) :
    latticeIntegerVector k = ∑ i, (k i : ℝ) • EuclideanSpace.single i 1 := by
  ext j
  cases j with
  | none => simp [latticeIntegerVector]
  | some j => simp [latticeIntegerVector, Pi.single_apply]

theorem inner_lattice_integer {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (ξ : OAI.Analysis.Calculus.Current.SpatialSpace d)
    (m : Option (Fin d) → ℤ)
    (hm : ∀ i, inner ℝ ξ (R (EuclideanSpace.single i 1)) = (m i : ℝ) * (2 * Real.pi) / 100)
    (k : Option (Fin d) → ℤ) :
    inner ℝ ξ ((100 : ℝ) • R (latticeIntegerVector k)) =
      ((∑ i, k i * m i : ℤ) : ℝ) * (2 * Real.pi) := by
  rw [inner_smul_right, latticeIntegerVector_eq_sum, map_sum, inner_sum]
  simp only [map_smul, inner_smul_right, hm]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem packetCycleFrequency_lattice_integer {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (κ : ℝ) (v : Fin d → ℝ)
    (m : Option (Fin d) → ℤ)
    (hm : ∀ i, inner ℝ (packetSpatialFrequency κ v) (R (EuclideanSpace.single i 1)) =
      (m i : ℝ) * (2 * Real.pi) / 100)
    (k : Option (Fin d) → ℤ) :
    inner ℝ ((100 : ℝ) • R (latticeIntegerVector k)) (packetCycleFrequency κ v) =
      ((∑ i, k i * m i : ℤ) : ℝ) := by
  rw [packetCycleFrequency, inner_smul_right, real_inner_comm,
    inner_lattice_integer R _ m hm k]
  field_simp

end OAI.Analysis.PDE.Concentration
