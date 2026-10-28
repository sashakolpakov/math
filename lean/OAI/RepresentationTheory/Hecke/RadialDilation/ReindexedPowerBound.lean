import OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex
import OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticSwap

/-! # Reindexed Power Bound -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.ReindexedPowerBound.Realization

noncomputable section

/-! Reindexing and swapping phase coordinates preserve entrywise bounds on matrix powers. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

theorem symplecticSwapHom_entry {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]
    (g : Theta.PoissonAutomorphyNormalizationData.Sp I K) (i j : Sum I I) :
    (SymplecticSwap.Realization.symplecticSwapHom g).val i j = g.val (Sum.swap i) (Sum.swap j) := by
  have h := Theta.PoissonAutomorphyNormalizationData.coordinateSwap_conjugation g.val.toBlocks₁₁ g.val.toBlocks₁₂ g.val.toBlocks₂₁ g.val.toBlocks₂₂
  rw [Matrix.fromBlocks_toBlocks] at h
  change (SymplecticSwap.Realization.symplecticSwapHom g).val = Matrix.fromBlocks g.val.toBlocks₂₂ g.val.toBlocks₂₁
    g.val.toBlocks₁₂ g.val.toBlocks₁₁ at h
  rw [h]
  cases i <;> cases j <;> rfl

theorem reindexed_swapped_power_bound (q : ℕ) [Fact q.Prime]
    {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} (e : I ≃ Fin n)
    (A : Theta.PoissonAutomorphyNormalizationData.Sp I ℚ_[q]) (R : ℝ) (hA : ∀ (N : ℕ) i j, ‖(A ^ N).val i j‖ ≤ R) :
    ∀ (N : ℕ) i j, ‖((SymplecticSwap.Realization.symplecticSwapHom (PositionReindex.Realization.symplecticReindex e A)) ^ N).val i j‖ ≤ R := by
  intro N i j
  rw [← map_pow, ← map_pow, symplecticSwapHom_entry]
  exact hA N ((e.sumCongr e).symm (Sum.swap i)) ((e.sumCongr e).symm (Sum.swap j))

end

end OAI.RepresentationTheory.Hecke.RadialDilation.ReindexedPowerBound.Realization
