import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PeriodTotal
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # Oscillator Phase Order -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.OscillatorPhaseOrder.CM

noncomputable section

section

/-! ThetaCycle: reindex the actual total rational change of splitting into the
finite-coordinate symplectic group used by the native oscillator. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

section Reindex

variable {I J R : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [CommRing R]

theorem reindex_symplectic_J (e : I ≃ J) :
    Matrix.reindexRingEquiv R (e.sumCongr e) (Matrix.J I R) = Matrix.J J R := by
  ext i j
  change Matrix.J I R ((e.sumCongr e).symm i) ((e.sumCongr e).symm j) = Matrix.J J R i j
  cases i <;> cases j <;>
    simp [Matrix.J, Matrix.fromBlocks, Matrix.one_apply]

def reindexSymplectic (e : I ≃ J) : Matrix.symplecticGroup I R →* Matrix.symplecticGroup J R where
  toFun g := ⟨Matrix.reindexRingEquiv R (e.sumCongr e) g.val, by
    apply SymplecticGroup.mem_iff.mpr
    have h := congrArg (Matrix.reindexRingEquiv R (e.sumCongr e))
      (SymplecticGroup.mem_iff.mp g.property)
    have ht : Matrix.reindexRingEquiv R (e.sumCongr e) g.val.transpose =
        (Matrix.reindexRingEquiv R (e.sumCongr e) g.val).transpose :=
      (Matrix.transpose_reindex _ _ _).symm
    simpa only [map_mul, reindex_symplectic_J, ht] using h⟩
  map_one' := Subtype.ext (map_one (Matrix.reindexRingEquiv R (e.sumCongr e)))
  map_mul' g h := Subtype.ext (map_mul (Matrix.reindexRingEquiv R (e.sumCongr e)) g.val h.val)

theorem reindex_symplectic_entry (e : I ≃ J) (g : Matrix.symplecticGroup I R)
    (i j : J ⊕ J) :
    (reindexSymplectic e g).val i j = g.val ((e.sumCongr e).symm i) ((e.sumCongr e).symm j) := rfl

end Reindex

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [NumberField.IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase)

def approximationOscillatorMatrix {ε : ℝ}
    (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε) :
    Matrix.symplecticGroup (Fin (Fintype.card (PeriodTotal.CM.TotalPositions K D.places))) ℚ :=
  reindexSymplectic (Fintype.equivFin (PeriodTotal.CM.TotalPositions K D.places)) (PeriodTotal.CM.approximationSymplecticMatrix K D A)

theorem approximation_oscillator_matrix_entry {ε : ℝ}
    (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
    (i j : PeriodTotal.CM.TotalPositions K D.places ⊕ PeriodTotal.CM.TotalPositions K D.places) :
    (approximationOscillatorMatrix K D A).val
      ((Fintype.equivFin _).sumCongr (Fintype.equivFin _) i)
      ((Fintype.equivFin _).sumCongr (Fintype.equivFin _) j) =
        (PeriodTotal.CM.approximationSymplecticMatrix K D A).val i j := by
  simp only [approximationOscillatorMatrix, reindex_symplectic_entry, Equiv.symm_apply_apply]

end

/-! ThetaCycle: explicit interchange of the classical [Z;1] graph order and
the oscillator [1;Z] order. Conjugating by this interchange preserves the
symplectic group even though the interchange itself reverses its pairing. -/

open scoped Classical _root_.Matrix

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

theorem swap_phase_J :
    Matrix.reindexRingEquiv R (Equiv.sumComm I I) (Matrix.J I R) = -Matrix.J I R := by
  ext i j
  change Matrix.J I R ((Equiv.sumComm I I).symm i) ((Equiv.sumComm I I).symm j) =
    -(Matrix.J I R i j)
  cases i <;> cases j <;> simp [Matrix.J, Matrix.fromBlocks, Matrix.one_apply]

def swapSymplecticPhase : Matrix.symplecticGroup I R →* Matrix.symplecticGroup I R where
  toFun g := ⟨Matrix.reindexRingEquiv R (Equiv.sumComm I I) g.val, by
    apply SymplecticGroup.mem_iff.mpr
    have h := congrArg (Matrix.reindexRingEquiv R (Equiv.sumComm I I))
      (SymplecticGroup.mem_iff.mp g.property)
    have ht : Matrix.reindexRingEquiv R (Equiv.sumComm I I) g.val.transpose =
        (Matrix.reindexRingEquiv R (Equiv.sumComm I I) g.val).transpose :=
      (Matrix.transpose_reindex _ _ _).symm
    simpa only [map_mul, swap_phase_J, ht, Matrix.mul_neg, Matrix.neg_mul, neg_inj] using h⟩
  map_one' := Subtype.ext (map_one (Matrix.reindexRingEquiv R (Equiv.sumComm I I)))
  map_mul' g h := Subtype.ext (map_mul (Matrix.reindexRingEquiv R (Equiv.sumComm I I)) g.val h.val)

theorem swap_symplectic_phase_blocks (g : Matrix.symplecticGroup I R) :
    (swapSymplecticPhase g).val = Matrix.fromBlocks g.val.toBlocks₂₂ g.val.toBlocks₂₁
      g.val.toBlocks₁₂ g.val.toBlocks₁₁ := by
  ext i j
  cases i <;> cases j <;> rfl

theorem swap_symplectic_phase_involutive (g : Matrix.symplecticGroup I R) :
    swapSymplecticPhase (swapSymplecticPhase g) = g := by
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;> rfl

theorem swap_symplectic_phase_graph (g : Matrix.symplecticGroup I R) (Z : Matrix I I R) :
    (swapSymplecticPhase g).val * Matrix.fromRows 1 Z =
      Matrix.fromRows (g.val.toBlocks₂₁ * Z + g.val.toBlocks₂₂)
        (g.val.toBlocks₁₁ * Z + g.val.toBlocks₁₂) := by
  rw [swap_symplectic_phase_blocks]
  simpa only [mul_one, add_comm] using!
    Matrix.fromBlocks_mul_fromRows (1 : Matrix I I R) Z g.val.toBlocks₂₂ g.val.toBlocks₂₁
      g.val.toBlocks₁₂ g.val.toBlocks₁₁

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.OscillatorPhaseOrder.CM
