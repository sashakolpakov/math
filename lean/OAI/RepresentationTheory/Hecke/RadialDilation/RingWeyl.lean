import OAI.RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator

/-! # Ring Weyl -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.RingWeyl.Realization

noncomputable section

/-! Weyl conjugation and its order over the coefficient rings used by RadialDilation. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (K : Type*) [CommRing K]

def ringWeyl : Theta.PoissonAutomorphyNormalizationData.Sp ι K := by
  refine ⟨Matrix.fromBlocks 0 (-1) 1 0, ?_⟩
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp

theorem ringWeyl_fourth : (ringWeyl K (ι := ι)) ^ 4 = 1 := by
  apply Subtype.ext
  change (Matrix.fromBlocks (0 : Matrix ι ι K) (-1) 1 0) ^ 4 = 1
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
  simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem map_ringWeyl {L : Type*} [CommRing L] (f : K →+* L) :
    Theta.PoissonAutomorphyNormalizationData.mapSp f (ringWeyl K (ι := ι)) = ringWeyl L := by
  apply Subtype.ext
  change (Matrix.fromBlocks (0 : Matrix ι ι K) (-1) 1 0).map f =
    Matrix.fromBlocks 0 (-1) 1 0
  simp [Matrix.fromBlocks_map]
  apply Matrix.ext
  intro i j
  change f (-(if i = j then 1 else 0)) = -(if i = j then 1 else 0)
  by_cases hij : i = j <;> simp [hij]

def ringLower (B : Matrix ι ι K) (hB : B.IsSymm) : Theta.PoissonAutomorphyNormalizationData.Sp ι K := by
  refine ⟨Matrix.fromBlocks 1 0 B 1, ?_⟩
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp [hB.eq]

theorem ringLower_conjugation (B : Matrix ι ι K) (hB : B.IsSymm) :
    ringLower K B hB = ringWeyl K * QuadraticCommutator.Realization.ringUpper (-B) hB.neg * (ringWeyl K)⁻¹ := by
  apply Subtype.ext
  change Matrix.fromBlocks 1 0 B 1 =
    (ringWeyl K).val * (QuadraticCommutator.Realization.ringUpper (-B) hB.neg).val * ((ringWeyl K)⁻¹).val
  rw [SymplecticGroup.coe_inv]
  simp [ringWeyl, QuadraticCommutator.Realization.ringUpper, Matrix.J, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.RingWeyl.Realization
