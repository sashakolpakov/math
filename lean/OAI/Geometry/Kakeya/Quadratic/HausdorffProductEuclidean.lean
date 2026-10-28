import OAI.Geometry.Kakeya.Quadratic.HausdorffProductDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set _root_.MeasureTheory Metric Module
open scoped ENNReal Topology

noncomputable section
namespace OAI.Geometry.Kakeya.Quadratic

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

omit [SecondCountableTopology X] in
theorem dimH_prod_cube_le (A : Set X) (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    dimH (A ×ˢ Set.pi Set.univ (fun _ : Fin n => Icc (-R) R)) ≤ dimH A + n := by
  have hT : dimH (Set.pi Set.univ (fun _ : Fin n => Icc (-R) R)) ≤ ENNReal.ofReal (n : ℝ) := by
    calc
      _ ≤ dimH (univ : Set (Fin n → ℝ)) := dimH_mono (subset_univ _)
      _ = ENNReal.ofReal (n : ℝ) := by rw [Real.dimH_univ_eq_finrank]; simp
  simpa using dimH_prod_le_of_finitePowerCover (Nat.cast_nonneg n)
    (C := ENNReal.ofReal (2*R+1)^n) (by finiteness) A (finitePowerCover_cube n hR) hT

omit [SecondCountableTopology X] in
theorem dimH_prod_univ_fin_le (A : Set X) (n : ℕ) :
    dimH (A ×ˢ (univ : Set (Fin n → ℝ))) ≤ dimH A + n := by
  let T (R : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Icc (-(R:ℝ)) (R:ℝ))
  have hcover : A ×ˢ (univ : Set (Fin n → ℝ)) = ⋃ R : ℕ, A ×ˢ T R := by
    ext p
    constructor
    · intro hp
      obtain ⟨R, hR⟩ := exists_nat_ge ‖p.2‖
      refine mem_iUnion.mpr ⟨R, hp.1, ?_⟩
      intro i hi
      have hv0 : |p.2 i| ≤ ‖p.2‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm p.2 i
      have hv : |p.2 i| ≤ (R : ℝ) := hv0.trans hR
      exact abs_le.mp hv
    · intro hp
      obtain ⟨R, hR⟩ := mem_iUnion.mp hp
      exact ⟨hR.1, mem_univ _⟩
  rw [hcover, dimH_iUnion]
  exact iSup_le fun R => dimH_prod_cube_le A n (Nat.cast_nonneg R)

theorem dimH_prod_univ_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (A : Set E) :
    dimH (A ×ˢ (univ : Set F)) ≤ dimH A + finrank ℝ F := by
  borelize E
  let e : F ≃L[ℝ] (Fin (finrank ℝ F) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  let d := (ContinuousLinearEquiv.refl ℝ E).prodCongr e
  have he : d '' (A ×ˢ (univ : Set F)) = A ×ˢ (univ : Set (Fin (finrank ℝ F) → ℝ)) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨hq.1, mem_univ _⟩
    · intro hp
      exact ⟨(p.1, e.symm p.2), ⟨hp.1, mem_univ _⟩, by simp [d]⟩
  rw [← d.dimH_image (A ×ˢ (univ : Set F)), he]
  exact dimH_prod_univ_fin_le A _

theorem dimH_prod_le_finrank {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (A : Set E) (T : Set F) :
    dimH (A ×ˢ T) ≤ dimH A + finrank ℝ F :=
  (dimH_mono (Set.prod_mono Subset.rfl (subset_univ _))).trans (dimH_prod_univ_le A)

end OAI.Geometry.Kakeya.Quadratic
