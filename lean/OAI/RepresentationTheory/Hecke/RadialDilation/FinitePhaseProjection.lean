import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteBlockIntertwiner
import OAI.RepresentationTheory.Hecke.RadialDilation.MatrixProjection

/-! # Finite Phase Projection -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FinitePhaseProjection.Realization

noncomputable section

/-! A finite-adelic matrix acts on a one-prime phase vector through its actual local projection. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable (q : ℕ) [Fact q.Prime]
variable {κ : Type*}

def finitePadicVector : (κ → ℚ_[q]) →ₗ[ℚ] (κ → Theta.PoissonAutomorphyNormalizationData.AQf) where
  toFun x i := FiniteSchur.Realization.finitePadicInclusion q (x i)
  map_add' x y := by
    funext i
    exact (FiniteSchur.Realization.finitePadicInclusion q).map_add (x i) (y i)
  map_smul' a x := by
    funext i
    exact (FiniteSchur.Realization.finitePadicInclusion q).map_smul a (x i)

theorem finitePadicVector_apply (x : κ → ℚ_[q]) (i : κ) :
    finitePadicVector q x i = FiniteSchur.Realization.finitePadicInclusion q (x i) := rfl

theorem finitePadic_mul_inclusion (a : Theta.PoissonAutomorphyNormalizationData.AQf) (x : ℚ_[q]) :
    a * FiniteSchur.Realization.finitePadicInclusion q x = FiniteSchur.Realization.finitePadicInclusion q (FiniteSchur.Realization.finitePadicProjection q a * x) := by
  rw [mul_comm a, FiniteBlockChart.Realization.finitePadicInclusion_mul]
  exact congrArg (FiniteSchur.Realization.finitePadicInclusion q) (mul_comm x (FiniteSchur.Realization.finitePadicProjection q a))

theorem finitePadic_sum_mul_inclusion [Fintype κ] (a : κ → Theta.PoissonAutomorphyNormalizationData.AQf) (x : κ → ℚ_[q]) :
    (∑ j, a j * FiniteSchur.Realization.finitePadicInclusion q (x j)) =
      FiniteSchur.Realization.finitePadicInclusion q (∑ j, FiniteSchur.Realization.finitePadicProjection q (a j) * x j) := by
  rw [map_sum]
  exact Finset.sum_congr rfl (fun j _ => finitePadic_mul_inclusion q (a j) (x j))

theorem finiteMatrix_mul_localVector [Fintype κ] (A : Matrix κ κ Theta.PoissonAutomorphyNormalizationData.AQf) (x : κ → ℚ_[q]) :
    A *ᵥ finitePadicVector q x = finitePadicVector q (A.map (FiniteSchur.Realization.finitePadicProjection q) *ᵥ x) := by
  exact MatrixProjection.Realization.matrix_mul_projected_vector (FiniteSchur.Realization.finitePadicProjection q).toRingHom
    (FiniteSchur.Realization.finitePadicInclusion q).toAddMonoidHom (finitePadic_mul_inclusion q) A x

variable {Place : Type*} (μ : Place)

def localBlockPhase (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3) : Sum (Place × Fin 3) (Place × Fin 3) → ℚ_[q] :=
  Sum.elim (fun p => if p.1 = μ then v (Sum.inr p.2) else 0)
    (fun p => if p.1 = μ then v (Sum.inl p.2) else 0)

theorem finiteBlockPhase_eq_localVector (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3) :
    FiniteBlockIntertwiner.Realization.finiteBlockPhase q μ v = finitePadicVector q (localBlockPhase q μ v) := by
  funext j
  cases j with
  | inl p =>
      change FiniteBlockChart.Realization.finiteBlockInclusion q μ (fun i => v (Sum.inr i)) p =
        FiniteSchur.Realization.finitePadicInclusion q (if p.1 = μ then v (Sum.inr p.2) else 0)
      rw [FiniteBlockChart.Realization.finiteBlockInclusion_apply]
      split_ifs <;> simp
  | inr p =>
      change FiniteBlockChart.Realization.finiteBlockInclusion q μ (fun i => v (Sum.inl i)) p =
        FiniteSchur.Realization.finitePadicInclusion q (if p.1 = μ then v (Sum.inl p.2) else 0)
      rw [FiniteBlockChart.Realization.finiteBlockInclusion_apply]
      split_ifs <;> simp

theorem finiteMatrix_localBlock_action [Fintype Place]
    (A : Matrix (Sum (Place × Fin 3) (Place × Fin 3)) (Sum (Place × Fin 3) (Place × Fin 3)) Theta.PoissonAutomorphyNormalizationData.AQf)
    (φ : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3 → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3)
    (hA : ∀ v, A.map (FiniteSchur.Realization.finitePadicProjection q) *ᵥ localBlockPhase q μ v = localBlockPhase q μ (φ v))
    (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3) : A *ᵥ FiniteBlockIntertwiner.Realization.finiteBlockPhase q μ v = FiniteBlockIntertwiner.Realization.finiteBlockPhase q μ (φ v) := by
  rw [finiteBlockPhase_eq_localVector, finiteMatrix_mul_localVector, hA, finiteBlockPhase_eq_localVector]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FinitePhaseProjection.Realization
