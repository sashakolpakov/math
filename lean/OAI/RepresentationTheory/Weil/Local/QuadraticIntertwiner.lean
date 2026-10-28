import OAI.RepresentationTheory.Weil.Local.LinearIntertwiner
import OAI.RepresentationTheory.Weil.Local.RealTestSpace

/-! # Quadratic Intertwiner -/

namespace OAI.RepresentationTheory.Weil.Local.QuadraticIntertwiner.Construction

noncomputable section

section

/-! Quadratic Heisenberg intertwiners on the concrete test-function space. -/

open _root_.Matrix _root_.MeasureTheory
open scoped BigOperators

theorem quadratic_eq_dot {k : Type} [Field k] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) k) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.quadratic B x = FunctionsMetaplectic.Construction.dot x (B *ᵥ x) / 2 := by
  simp [FunctionsMetaplectic.Construction.quadratic, FunctionsMetaplectic.Construction.dot, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem quadratic_sub {k : Type} [Field k] [CharZero k] {n : ℕ}
    (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (x q : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.quadratic B.val x - FunctionsMetaplectic.Construction.quadratic B.val (x - q) =
      FunctionsMetaplectic.Construction.dot (B.val *ᵥ q) (x - (2 : k)⁻¹ • q) := by
  have hcross : FunctionsMetaplectic.Construction.dot q (B.val *ᵥ x) = FunctionsMetaplectic.Construction.dot x (B.val *ᵥ q) := by
    change q ⬝ᵥ B.val *ᵥ x = x ⬝ᵥ B.val *ᵥ q
    simpa only [B.property.eq] using Matrix.dotProduct_transpose_mulVec B.val q x
  rw [quadratic_eq_dot, quadratic_eq_dot, FourierTools.Construction.dot_comm (B.val *ᵥ q)]
  change (x ⬝ᵥ B.val *ᵥ x) / 2 - ((x - q) ⬝ᵥ B.val *ᵥ (x - q)) / 2 =
    (x - (2 : k)⁻¹ • q) ⬝ᵥ B.val *ᵥ q
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct,
    smul_dotProduct, smul_eq_mul]
  change FunctionsMetaplectic.Construction.dot x (B.val *ᵥ x) / 2 -
    (FunctionsMetaplectic.Construction.dot x (B.val *ᵥ x) - FunctionsMetaplectic.Construction.dot q (B.val *ᵥ x) -
      (FunctionsMetaplectic.Construction.dot x (B.val *ᵥ q) - FunctionsMetaplectic.Construction.dot q (B.val *ᵥ q))) / 2 = _
  rw [hcross]
  unfold FunctionsMetaplectic.Construction.dot dotProduct
  ring

theorem positionPart_quadratic {k : Type} [Field k] {n : ℕ}
    (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (v : FunctionsMetaplectic.Construction.PhaseSpace k n) :
    LinearIntertwiner.Construction.positionPart (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.quadraticSymplectic B) v) = LinearIntertwiner.Construction.positionPart v := by
  funext i
  simp [LinearIntertwiner.Construction.positionPart, FunctionsMetaplectic.Construction.symplecticAction, Generators.Construction.quadraticSymplectic_matrix,
    Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]

theorem momentumPart_quadratic {k : Type} [Field k] {n : ℕ}
    (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (v : FunctionsMetaplectic.Construction.PhaseSpace k n) :
    LinearIntertwiner.Construction.momentumPart (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.quadraticSymplectic B) v) =
      B.val *ᵥ LinearIntertwiner.Construction.positionPart v + LinearIntertwiner.Construction.momentumPart v := by
  funext i
  simp [LinearIntertwiner.Construction.positionPart, LinearIntertwiner.Construction.momentumPart, FunctionsMetaplectic.Construction.symplecticAction, Generators.Construction.quadraticSymplectic_matrix,
    Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]

theorem quadraticOperator_heisenberg {k : Type} [Field k] [CharZero k] {n : ℕ}
    (ψ : AddChar k ℂ) (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (v : FunctionsMetaplectic.Construction.PhaseSpace k n)
    (f : FunctionsMetaplectic.Construction.Position k n → ℂ) :
    FunctionsMetaplectic.Construction.quadraticOperator ψ B.val (FunctionsMetaplectic.Construction.heisenbergFunction ψ v f) =
      FunctionsMetaplectic.Construction.heisenbergFunction ψ (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.quadraticSymplectic B) v)
        (FunctionsMetaplectic.Construction.quadraticOperator ψ B.val f) := by
  funext x
  rw [FunctionsMetaplectic.Construction.quadraticOperator_apply, LinearIntertwiner.Construction.heisenbergFunction_eq_dot, LinearIntertwiner.Construction.heisenbergFunction_eq_dot,
    positionPart_quadratic, momentumPart_quadratic, FunctionsMetaplectic.Construction.quadraticOperator_apply,
    ← mul_assoc, ← mul_assoc, ← ψ.map_add_eq_mul, ← ψ.map_add_eq_mul]
  congr 2
  change FunctionsMetaplectic.Construction.quadratic B.val x + FunctionsMetaplectic.Construction.dot (LinearIntertwiner.Construction.momentumPart v) (x - (2 : k)⁻¹ • LinearIntertwiner.Construction.positionPart v) =
    FunctionsMetaplectic.Construction.dot (B.val *ᵥ LinearIntertwiner.Construction.positionPart v + LinearIntertwiner.Construction.momentumPart v)
      (x - (2 : k)⁻¹ • LinearIntertwiner.Construction.positionPart v) + FunctionsMetaplectic.Construction.quadratic B.val (x - LinearIntertwiner.Construction.positionPart v)
  have h := quadratic_sub B x (LinearIntertwiner.Construction.positionPart v)
  simp only [FunctionsMetaplectic.Construction.dot, Pi.add_apply, add_mul, Finset.sum_add_distrib] at *
  linear_combination h

section Restriction

variable {k : Type} [NormedField k] {n : ℕ} (ψ : AddChar k ℂ)
    (hStable : ∀ (B : Matrix (Fin n) (Fin n) k) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n),
      FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val ∈ FunctionsMetaplectic.Construction.schwartzBruhat k n)

def testQuadratic (B : Matrix (Fin n) (Fin n) k) :
    FunctionsMetaplectic.Construction.schwartzBruhat k n ≃ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat k n where
  toFun f := ⟨FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val, hStable B f⟩
  invFun f := ⟨FunctionsMetaplectic.Construction.quadraticOperator ψ (-B) f.val, hStable (-B) f⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    change ψ (FunctionsMetaplectic.Construction.quadratic (-B) x) * (ψ (FunctionsMetaplectic.Construction.quadratic B x) * f.val x) = f.val x
    rw [FunctionsMetaplectic.Construction.quadratic_neg, ← mul_assoc, ← ψ.map_add_eq_mul]
    simp
  right_inv f := by
    apply Subtype.ext
    funext x
    change ψ (FunctionsMetaplectic.Construction.quadratic B x) * (ψ (FunctionsMetaplectic.Construction.quadratic (-B) x) * f.val x) = f.val x
    rw [FunctionsMetaplectic.Construction.quadratic_neg, ← mul_assoc, ← ψ.map_add_eq_mul]
    simp
  map_add' f g := Subtype.ext ((FunctionsMetaplectic.Construction.quadraticOperator ψ B).map_add f.val g.val)
  map_smul' c f := Subtype.ext ((FunctionsMetaplectic.Construction.quadraticOperator ψ B).map_smul c f.val)

theorem testQuadratic_val (B : Matrix (Fin n) (Fin n) k) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    (testQuadratic ψ hStable B f).val = FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val := rfl

theorem testQuadratic_intertwines [CharZero k] (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n)
    (v : FunctionsMetaplectic.Construction.PhaseSpace k n) (f h : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    FunctionsMetaplectic.Construction.heisenbergGraph ψ v f h ↔
      FunctionsMetaplectic.Construction.heisenbergGraph ψ (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.quadraticSymplectic B) v)
        (testQuadratic ψ hStable B.val f) (testQuadratic ψ hStable B.val h) := by
  unfold FunctionsMetaplectic.Construction.heisenbergGraph
  rw [testQuadratic_val, testQuadratic_val, ← quadraticOperator_heisenberg]
  exact (FunctionsMetaplectic.Construction.quadraticOperator ψ B.val).injective.eq_iff.symm

def quadraticOscillator [CharZero k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k]
    (hUnitary : ∀ t : k, ‖ψ t‖ = 1) (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) : FunctionsMetaplectic.Construction.Oscillator k n ψ :=
  ⟨(Generators.Construction.quadraticSymplectic B, testQuadratic ψ hStable B.val), by
    constructor
    · intro f
      unfold FunctionsMetaplectic.Construction.l2Energy
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change ‖FunctionsMetaplectic.Construction.quadraticOperator ψ B.val f.val x‖ ^ 2 = ‖f.val x‖ ^ 2
        rw [Generators.Construction.quadraticOperator_norm ψ hUnitary]
    · exact testQuadratic_intertwines ψ hStable B⟩

end Restriction

theorem realCharacter_unitary (c t : ℝ) : ‖Gaussian.Construction.realCharacter c t‖ = 1 := by
  change ‖(Real.fourierChar (c * t) : ℂ)‖ = 1
  exact Circle.norm_coe _

def realQuadraticOscillator {n : ℕ} (c : ℝ) (B : FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n) :
    FunctionsMetaplectic.Construction.Oscillator ℝ n (Gaussian.Construction.realCharacter c) :=
  quadraticOscillator (Gaussian.Construction.realCharacter c)
    (fun B f => RealTestSpace.Construction.quadraticOperator_real_mem c B f.property) (realCharacter_unitary c) B

theorem realQuadraticOscillator_apply {n : ℕ} (c : ℝ) (B : FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    ((realQuadraticOscillator c B).val.2 f).val x =
      Gaussian.Construction.realCharacter c (FunctionsMetaplectic.Construction.quadratic B.val x) * f.val x := rfl

end

/-! The quadratic generator belongs to the intrinsically defined bare subgroup. -/

open _root_.Matrix
open scoped BigOperators commutatorElement

def symmetricScale {k : Type} [Field k] {n : ℕ}
    (a : k) (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) : FunctionsMetaplectic.Construction.SymmetricMatrix k n :=
  ⟨a • B.val, B.property.smul a⟩

theorem quadratic_smul_matrix {k : Type} [Field k] {n : ℕ}
    (a : k) (B : Matrix (Fin n) (Fin n) k) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.quadratic (a • B) x = a * FunctionsMetaplectic.Construction.quadratic B x := by
  simp only [FunctionsMetaplectic.Construction.quadratic, Matrix.smul_apply, smul_eq_mul]
  rw [← mul_div_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadratic_smul_vector {k : Type} [Field k] {n : ℕ}
    (a : k) (B : Matrix (Fin n) (Fin n) k) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.quadratic B (a • x) = a ^ 2 * FunctionsMetaplectic.Construction.quadratic B x := by
  simp only [FunctionsMetaplectic.Construction.quadratic, Pi.smul_apply, smul_eq_mul]
  rw [← mul_div_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

def halfScalarMatrix (k : Type) [Field k] [CharZero k] (n : ℕ) : FunctionsMetaplectic.Construction.GeneralLinear k n :=
  Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 (2 : k) (by norm_num))⁻¹

theorem halfScalarMatrix_val (k : Type) [Field k] [CharZero k] (n : ℕ) :
    (halfScalarMatrix k n : Matrix (Fin n) (Fin n) k) =
      (2 : k)⁻¹ • (1 : Matrix (Fin n) (Fin n) k) := by
  change Matrix.scalar (Fin n) (2 : k)⁻¹ = _
  simp [← Matrix.diagonal_smul, ← Matrix.diagonal_one]

theorem halfScalarMatrix_inv_val (k : Type) [Field k] [CharZero k] (n : ℕ) :
    (↑((halfScalarMatrix k n)⁻¹) : Matrix (Fin n) (Fin n) k) =
      (2 : k) • (1 : Matrix (Fin n) (Fin n) k) := by
  simp [halfScalarMatrix, ← map_inv, ← Matrix.diagonal_smul, ← Matrix.diagonal_one]

section Local

variable {k : Type} [NormedField k] [CharZero k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (hUnitary : ∀ t : k, ‖ψ t‖ = 1)
    (hStable : ∀ (B : Matrix (Fin n) (Fin n) k) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n),
      FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val ∈ FunctionsMetaplectic.Construction.schwartzBruhat k n)

theorem quadratic_commutator_relation (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) :
    LinearIntertwiner.Construction.linearOscillator ψ (halfScalarMatrix k n) *
        quadraticOscillator ψ hStable hUnitary (symmetricScale (3 : k)⁻¹ B) =
      quadraticOscillator ψ hStable hUnitary B *
        quadraticOscillator ψ hStable hUnitary (symmetricScale (3 : k)⁻¹ B) *
        LinearIntertwiner.Construction.linearOscillator ψ (halfScalarMatrix k n) := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    change (Generators.Construction.leviSymplectic (halfScalarMatrix k n) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) *
        (Generators.Construction.quadraticSymplectic (symmetricScale (3 : k)⁻¹ B) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) =
      (Generators.Construction.quadraticSymplectic B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) *
        (Generators.Construction.quadraticSymplectic (symmetricScale (3 : k)⁻¹ B) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) *
        (Generators.Construction.leviSymplectic (halfScalarMatrix k n) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)
    simp only [Generators.Construction.leviSymplectic_matrix, Generators.Construction.quadraticSymplectic_matrix,
      halfScalarMatrix_val, halfScalarMatrix_inv_val, Matrix.transpose_smul,
      Matrix.transpose_one, Matrix.fromBlocks_multiply, symmetricScale,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.smul_mul, Matrix.mul_smul, zero_add, add_zero]
    congr 1 <;> ext i j <;>
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.zero_apply, smul_eq_mul] <;> ring
  · apply LinearEquiv.ext
    intro f
    apply Subtype.ext
    funext x
    change ((LinearIntertwiner.Construction.linearOscillator ψ (halfScalarMatrix k n)).val.2
        (testQuadratic ψ hStable ((3 : k)⁻¹ • B.val) f)).val x =
      (testQuadratic ψ hStable B.val
        (testQuadratic ψ hStable ((3 : k)⁻¹ • B.val)
          ((LinearIntertwiner.Construction.linearOscillator ψ (halfScalarMatrix k n)).val.2 f))).val x
    simp only [LinearIntertwiner.Construction.linearOscillator_apply, testQuadratic_val, FunctionsMetaplectic.Construction.quadraticOperator_apply,
      halfScalarMatrix_inv_val, Matrix.smul_mulVec, Matrix.one_mulVec,
      quadratic_smul_vector, quadratic_smul_matrix]
    have hphase : (2 : k) ^ 2 * ((3 : k)⁻¹ * FunctionsMetaplectic.Construction.quadratic B.val x) =
        FunctionsMetaplectic.Construction.quadratic B.val x + (3 : k)⁻¹ * FunctionsMetaplectic.Construction.quadratic B.val x := by ring
    rw [hphase, ψ.map_add_eq_mul]
    ring

theorem quadraticOscillator_mem_metaplectic (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) :
    quadraticOscillator ψ hStable hUnitary B ∈ FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ := by
  apply Subgroup.subset_closure
  left
  refine ⟨LinearIntertwiner.Construction.linearOscillator ψ (halfScalarMatrix k n),
    quadraticOscillator ψ hStable hUnitary (symmetricScale (3 : k)⁻¹ B), ?_⟩
  rw [commutatorElement_def, quadratic_commutator_relation ψ hUnitary hStable B]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

def quadraticMetaplectic (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) : FunctionsMetaplectic.Construction.Metaplectic k n ψ :=
  ⟨quadraticOscillator ψ hStable hUnitary B,
    quadraticOscillator_mem_metaplectic ψ hUnitary hStable B⟩

theorem quadraticMetaplectic_projection (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) :
    FunctionsMetaplectic.Construction.metaplecticProjection k n ψ (quadraticMetaplectic ψ hUnitary hStable B) =
      Generators.Construction.quadraticSymplectic B := rfl

theorem quadraticMetaplectic_apply (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
    (FunctionsMetaplectic.Construction.weilRepresentation k n ψ (quadraticMetaplectic ψ hUnitary hStable B) f).val x =
      ψ (FunctionsMetaplectic.Construction.quadratic B.val x) * f.val x := rfl

end Local

/-- An actual bare metaplectic lift, with no realization or membership assumption,
for each real quadratic generator. -/
def realQuadraticMetaplectic {n : ℕ} (c : ℝ) (B : FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n) :
    FunctionsMetaplectic.Construction.Metaplectic ℝ n (Gaussian.Construction.realCharacter c) :=
  quadraticMetaplectic (Gaussian.Construction.realCharacter c) (realCharacter_unitary c)
    (fun B f => RealTestSpace.Construction.quadraticOperator_real_mem c B f.property) B

theorem realQuadraticMetaplectic_projection {n : ℕ} (c : ℝ) (B : FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n) :
    FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (Gaussian.Construction.realCharacter c) (realQuadraticMetaplectic c B) =
      Generators.Construction.quadraticSymplectic B := rfl

theorem realQuadraticMetaplectic_apply {n : ℕ} (c : ℝ) (B : FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    (FunctionsMetaplectic.Construction.weilRepresentation ℝ n (Gaussian.Construction.realCharacter c) (realQuadraticMetaplectic c B) f).val x =
      Gaussian.Construction.realCharacter c (FunctionsMetaplectic.Construction.quadratic B.val x) * f.val x := rfl

end

end OAI.RepresentationTheory.Weil.Local.QuadraticIntertwiner.Construction
