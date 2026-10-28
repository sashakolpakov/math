import OAI.Analysis.Fourier.Restriction.CellSeries

open OAI.Analysis.Fourier.Wave

open Filter
open scoped BigOperators Topology
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

def latticeBox (n N : ℕ) : Finset (Fin n → ℤ) :=
  Finset.Icc (fun _ ↦ -(N : ℤ)) (fun _ ↦ (N : ℤ))

theorem latticeBox_monotone (n : ℕ) : Monotone (latticeBox n) := by
  intro M N hMN k hk
  have hMN' : (M : ℤ) ≤ N := by exact_mod_cast hMN
  simp only [latticeBox, Finset.mem_Icc] at hk ⊢
  exact ⟨fun i ↦ (neg_le_neg hMN').trans (hk.1 i), fun i ↦ (hk.2 i).trans hMN'⟩

theorem exists_mem_latticeBox {n : ℕ} (k : Fin n → ℤ) : ∃ N, k ∈ latticeBox n N := by
  classical
  let N := Finset.univ.sup (fun i : Fin n ↦ (k i).natAbs)
  have hi (i : Fin n) : |k i| ≤ (N : ℤ) := by
    have H : (k i).natAbs ≤ N := Finset.le_sup (f := fun i : Fin n ↦ (k i).natAbs) (Finset.mem_univ i)
    rw [← Int.natCast_natAbs]
    exact_mod_cast H
  refine ⟨N, ?_⟩
  simp only [latticeBox, Finset.mem_Icc]
  exact ⟨fun i ↦ (abs_le.mp (hi i)).1, fun i ↦ (abs_le.mp (hi i)).2⟩

theorem tendsto_latticeBox (n : ℕ) : Tendsto (latticeBox n) atTop atTop :=
  (latticeBox_monotone n).tendsto_atTop_finset exists_mem_latticeBox

theorem tendsto_unitCell_integral_boxes {n : ℕ} {f : Space n → ℂ} (hf : MeasureTheory.Integrable f) :
    Tendsto (fun N ↦ ∑ k ∈ latticeBox n N,
      ∫ y in OAI.Analysis.Fourier.WavePackets.unitCell n, f (OAI.Analysis.Fourier.WavePackets.integerVector k + y))
      atTop (𝓝 (∫ x, f x)) :=
  (hasSum_unitCell_integrals hf).comp (tendsto_latticeBox n)

end OAI.Analysis.Fourier.Restriction
