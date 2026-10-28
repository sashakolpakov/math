import OAI.RepresentationTheory.Weil.Local.DeterminantMeasure
import OAI.RepresentationTheory.Weil.Local.Generators

/-! # Linear Intertwiner -/

namespace OAI.RepresentationTheory.Weil.Local.LinearIntertwiner.Construction

noncomputable section

/-! Actual linear-substitution lifts to the Heisenberg oscillator extension. -/

open _root_.Matrix _root_.MeasureTheory
open scoped BigOperators

def positionPart {k : Type} {n : ℕ} (v : FunctionsMetaplectic.Construction.PhaseSpace k n) : FunctionsMetaplectic.Construction.Position k n :=
  fun i => v (Sum.inl i)

def momentumPart {k : Type} {n : ℕ} (v : FunctionsMetaplectic.Construction.PhaseSpace k n) : FunctionsMetaplectic.Construction.Position k n :=
  fun i => v (Sum.inr i)

theorem heisenbergFunction_eq_dot {k : Type} [Field k] {n : ℕ}
    (ψ : AddChar k ℂ) (v : FunctionsMetaplectic.Construction.PhaseSpace k n) (f : FunctionsMetaplectic.Construction.Position k n → ℂ) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.heisenbergFunction ψ v f x =
      ψ (FunctionsMetaplectic.Construction.dot (momentumPart v) (x - (2 : k)⁻¹ • positionPart v)) * f (x - positionPart v) := by
  unfold FunctionsMetaplectic.Construction.heisenbergFunction FunctionsMetaplectic.Construction.dot positionPart momentumPart
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  rw [mul_comm (2 : k)⁻¹]

theorem positionPart_levi {k : Type} [Field k] {n : ℕ}
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (v : FunctionsMetaplectic.Construction.PhaseSpace k n) :
    positionPart (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.leviSymplectic A) v) =
      (A : Matrix (Fin n) (Fin n) k) *ᵥ positionPart v := by
  funext i
  simp [positionPart, FunctionsMetaplectic.Construction.symplecticAction, Generators.Construction.leviSymplectic_matrix,
    Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks]

theorem momentumPart_levi {k : Type} [Field k] {n : ℕ}
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (v : FunctionsMetaplectic.Construction.PhaseSpace k n) :
    momentumPart (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.leviSymplectic A) v) =
      (↑(A⁻¹) : Matrix (Fin n) (Fin n) k).transpose *ᵥ momentumPart v := by
  funext i
  simp [momentumPart, FunctionsMetaplectic.Construction.symplecticAction, Generators.Construction.leviSymplectic_matrix,
    Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks]

theorem substitutionOperator_heisenberg {k : Type} [Field k] {n : ℕ}
    (ψ : AddChar k ℂ) (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (v : FunctionsMetaplectic.Construction.PhaseSpace k n)
    (f : FunctionsMetaplectic.Construction.Position k n → ℂ) :
    FunctionsMetaplectic.Construction.substitutionOperator A (FunctionsMetaplectic.Construction.heisenbergFunction ψ v f) =
      FunctionsMetaplectic.Construction.heisenbergFunction ψ (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.leviSymplectic A) v) (FunctionsMetaplectic.Construction.substitutionOperator A f) := by
  funext x
  rw [FunctionsMetaplectic.Construction.substitutionOperator_apply, heisenbergFunction_eq_dot, heisenbergFunction_eq_dot,
    positionPart_levi, momentumPart_levi, FunctionsMetaplectic.Construction.substitutionOperator_apply]
  have harg : (↑(A⁻¹) : Matrix (Fin n) (Fin n) k) *ᵥ
      (x - (↑A : Matrix (Fin n) (Fin n) k) *ᵥ positionPart v) =
      (↑(A⁻¹) : Matrix (Fin n) (Fin n) k) *ᵥ x - positionPart v := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [harg]
  congr 2
  symm
  rw [FourierTools.Construction.dot_comm]
  change (x - (2 : k)⁻¹ • ((↑A : Matrix (Fin n) (Fin n) k) *ᵥ positionPart v)) ⬝ᵥ
      (↑(A⁻¹) : Matrix (Fin n) (Fin n) k).transpose *ᵥ momentumPart v = _
  rw [Matrix.dotProduct_transpose_mulVec]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rfl

theorem heisenbergFunction_smul {k : Type} [Field k] {n : ℕ}
    (ψ : AddChar k ℂ) (v : FunctionsMetaplectic.Construction.PhaseSpace k n) (f : FunctionsMetaplectic.Construction.Position k n → ℂ) (c : ℂ) :
    FunctionsMetaplectic.Construction.heisenbergFunction ψ v (c • f) = c • FunctionsMetaplectic.Construction.heisenbergFunction ψ v f := by
  funext x
  simp only [FunctionsMetaplectic.Construction.heisenbergFunction, Pi.smul_apply, smul_eq_mul]
  exact mul_left_comm _ _ _

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}

def normalizedRawSubstitution (A : FunctionsMetaplectic.Construction.GeneralLinear k n) :
    (FunctionsMetaplectic.Construction.Position k n → ℂ) ≃ₗ[ℂ] (FunctionsMetaplectic.Construction.Position k n → ℂ) :=
  (FunctionsMetaplectic.Construction.substitutionOperator A).trans (LinearEquiv.smulOfUnit (LinearSubstitution.Construction.coordinateScaleUnit (LinearSubstitution.Construction.positionAddEquiv A)))

theorem normalizedRawSubstitution_val (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    normalizedRawSubstitution A f.val = (LinearSubstitution.Construction.normalizedCoordinate (LinearSubstitution.Construction.positionAddEquiv A) f).val := rfl

theorem normalizedRawSubstitution_heisenberg
    (ψ : AddChar k ℂ) (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (v : FunctionsMetaplectic.Construction.PhaseSpace k n) (f : FunctionsMetaplectic.Construction.Position k n → ℂ) :
    normalizedRawSubstitution A (FunctionsMetaplectic.Construction.heisenbergFunction ψ v f) =
      FunctionsMetaplectic.Construction.heisenbergFunction ψ (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.leviSymplectic A) v) (normalizedRawSubstitution A f) := by
  change (LinearSubstitution.Construction.coordinateScale (LinearSubstitution.Construction.positionAddEquiv A) : ℂ) • FunctionsMetaplectic.Construction.substitutionOperator A (FunctionsMetaplectic.Construction.heisenbergFunction ψ v f) =
    FunctionsMetaplectic.Construction.heisenbergFunction ψ (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.leviSymplectic A) v)
      ((LinearSubstitution.Construction.coordinateScale (LinearSubstitution.Construction.positionAddEquiv A) : ℂ) • FunctionsMetaplectic.Construction.substitutionOperator A f)
  rw [heisenbergFunction_smul, substitutionOperator_heisenberg]

theorem normalizedCoordinate_intertwines
    (ψ : AddChar k ℂ) (A : FunctionsMetaplectic.Construction.GeneralLinear k n)
    (v : FunctionsMetaplectic.Construction.PhaseSpace k n) (f h : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    FunctionsMetaplectic.Construction.heisenbergGraph ψ v f h ↔
      FunctionsMetaplectic.Construction.heisenbergGraph ψ (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.leviSymplectic A) v)
        (LinearSubstitution.Construction.normalizedCoordinate (LinearSubstitution.Construction.positionAddEquiv A) f) (LinearSubstitution.Construction.normalizedCoordinate (LinearSubstitution.Construction.positionAddEquiv A) h) := by
  unfold FunctionsMetaplectic.Construction.heisenbergGraph
  rw [← normalizedRawSubstitution_val, ← normalizedRawSubstitution_val,
    ← normalizedRawSubstitution_heisenberg]
  exact (normalizedRawSubstitution A).injective.eq_iff.symm

/-- This is an actual lift with the required positive determinant
normalization to the oscillator extension. Its bare-cover Weil-index
normalization is handled separately by the metaplectic argument. -/
def linearOscillator (ψ : AddChar k ℂ) (A : FunctionsMetaplectic.Construction.GeneralLinear k n) : FunctionsMetaplectic.Construction.Oscillator k n ψ :=
  ⟨(Generators.Construction.leviSymplectic A, LinearSubstitution.Construction.normalizedCoordinate (LinearSubstitution.Construction.positionAddEquiv A)),
    ⟨LinearSubstitution.Construction.normalizedCoordinate_l2Energy (LinearSubstitution.Construction.positionAddEquiv A), normalizedCoordinate_intertwines ψ A⟩⟩

theorem linearOscillator_apply (ψ : AddChar k ℂ) (A : FunctionsMetaplectic.Construction.GeneralLinear k n)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
    ((linearOscillator ψ A).val.2 f).val x =
      ((Real.sqrt (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A)))⁻¹ : ℂ) *
        f.val ((↑(A⁻¹) : Matrix (Fin n) (Fin n) k) *ᵥ x) :=
  DeterminantMeasure.Construction.normalizedCoordinate_matrix_apply A f x

end

end OAI.RepresentationTheory.Weil.Local.LinearIntertwiner.Construction
