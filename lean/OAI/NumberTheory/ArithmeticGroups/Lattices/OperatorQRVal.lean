import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRBasis
import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.TriangularMatrices

/-! # Operator QR Val -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRVal.Construction

noncomputable section

section

/-! Continuous compact and upper triangular factors of an invertible
operator, expressed in the chosen orthonormal basis. -/

open InnerProductSpace
open scoped Classical

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def operatorQRCompactMatrix {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (g : (L →L[ℝ] L)ˣ) :
    Matrix (Fin m) (Fin m) ℝ := b.toBasis.toMatrix (OperatorQRBasis.Construction.operatorQRBasis b g)

def operatorQRTriangularMatrix {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (g : (L →L[ℝ] L)ˣ) :
    Matrix (Fin m) (Fin m) ℝ := (OperatorQRBasis.Construction.operatorQRBasis b g).toBasis.toMatrix (fun i => g.val (b i))

theorem operatorQRCompactMatrix_entry {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : (L →L[ℝ] L)ˣ) (i j : Fin m) :
    operatorQRCompactMatrix b g i j = inner ℝ (b i) (OperatorQRBasis.Construction.operatorQRBasis b g j) := by
  change b.repr (OperatorQRBasis.Construction.operatorQRBasis b g j) i = _
  exact b.repr_apply_apply _ _

theorem operatorQRTriangularMatrix_entry {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : (L →L[ℝ] L)ˣ) (i j : Fin m) :
    operatorQRTriangularMatrix b g i j = inner ℝ (OperatorQRBasis.Construction.operatorQRBasis b g i) (g.val (b j)) := by
  change (OperatorQRBasis.Construction.operatorQRBasis b g).repr (g.val (b j)) i = _
  exact (OperatorQRBasis.Construction.operatorQRBasis b g).repr_apply_apply _ _

theorem operatorQRCompactMatrix_orthogonal {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : (L →L[ℝ] L)ˣ) : operatorQRCompactMatrix b g ∈ Matrix.orthogonalGroup (Fin m) ℝ :=
  b.toMatrix_orthonormalBasis_mem_orthogonal (OperatorQRBasis.Construction.operatorQRBasis b g)

theorem operatorQRTriangularMatrix_positive {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : (L →L[ℝ] L)ˣ) : Positive.TriangularMatrices.Construction.IsPositiveUpperTriangular (operatorQRTriangularMatrix b g) := by
  refine ⟨gramSchmidtOrthonormalBasis_inv_isUpperTriangular
    (Module.finrank_eq_card_basis b.toBasis) (fun i => g.val (b i)), fun i => ?_⟩
  rw [operatorQRTriangularMatrix_entry, OperatorQRBasis.Construction.operatorQRBasis_diagonal]
  exact OperatorQRBasis.Construction.operatorQRDiagonal_pos b g i

theorem operatorQR_factorization {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : (L →L[ℝ] L)ˣ) :
    ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val = operatorQRCompactMatrix b g * operatorQRTriangularMatrix b g := by
  have hM : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val = b.toBasis.toMatrix (fun i => g.val (b i)) := by
    ext i j
    exact LinearMap.toMatrix_apply b.toBasis b.toBasis g.val.toLinearMap i j
  rw [hM]
  exact (b.toBasis.toMatrix_mul_toMatrix (OperatorQRBasis.Construction.operatorQRBasis b g).toBasis (fun i => g.val (b i))).symm

theorem operatorQRCompactMatrix_continuous {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) :
    Continuous (operatorQRCompactMatrix b) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp_rw [operatorQRCompactMatrix_entry]
  exact continuous_const.inner (OperatorQRBasis.Construction.operatorQRBasis_continuous b j)

theorem operatorQRTriangularMatrix_continuous {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) :
    Continuous (operatorQRTriangularMatrix b) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp_rw [operatorQRTriangularMatrix_entry]
  exact (OperatorQRBasis.Construction.operatorQRBasis_continuous b i).inner (Units.continuous_val.clm_apply continuous_const)

end

section

/-! Splitting the positive diagonal from the triangular QR factor
gives continuous upper unitriangular coordinates. -/

open scoped Classical

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def operatorQRUnipotentMatrix {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (g : (L →L[ℝ] L)ˣ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal (fun i => (OperatorQRBasis.Construction.operatorQRDiagonal b g i)⁻¹) * operatorQRTriangularMatrix b g

theorem operatorQRUnipotentMatrix_entry {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : (L →L[ℝ] L)ˣ) (i j : Fin m) :
    operatorQRUnipotentMatrix b g i j = (OperatorQRBasis.Construction.operatorQRDiagonal b g i)⁻¹ * operatorQRTriangularMatrix b g i j :=
  Matrix.diagonal_mul _ _ i j

theorem operatorQRUnipotentMatrix_unitriangular {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : (L →L[ℝ] L)ˣ) : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (operatorQRUnipotentMatrix b g) := by
  have ht := (operatorQRTriangularMatrix_positive b g).1
  have hd : (Matrix.diagonal (fun i => (OperatorQRBasis.Construction.operatorQRDiagonal b g i)⁻¹)).IsUpperTriangular :=
    Matrix.blockTriangular_diagonal _
  refine ⟨hd.mul ht, fun i => ?_⟩
  rw [operatorQRUnipotentMatrix_entry, operatorQRTriangularMatrix_entry, OperatorQRBasis.Construction.operatorQRBasis_diagonal]
  exact inv_mul_cancel₀ (ne_of_gt (OperatorQRBasis.Construction.operatorQRDiagonal_pos b g i))

theorem operatorQR_diagonal_unipotent {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : (L →L[ℝ] L)ˣ) :
    Matrix.diagonal (OperatorQRBasis.Construction.operatorQRDiagonal b g) * operatorQRUnipotentMatrix b g =
      operatorQRTriangularMatrix b g := by
  ext i j
  rw [Matrix.diagonal_mul, operatorQRUnipotentMatrix_entry, ← mul_assoc,
    mul_inv_cancel₀ (ne_of_gt (OperatorQRBasis.Construction.operatorQRDiagonal_pos b g i)), one_mul]

theorem operatorQR_kan_factorization {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : (L →L[ℝ] L)ˣ) :
    ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val =
      operatorQRCompactMatrix b g * Matrix.diagonal (OperatorQRBasis.Construction.operatorQRDiagonal b g) * operatorQRUnipotentMatrix b g := by
  rw [mul_assoc, operatorQR_diagonal_unipotent]
  exact operatorQR_factorization b g

theorem operatorQRUnipotentMatrix_continuous {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) :
    Continuous (operatorQRUnipotentMatrix b) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp_rw [operatorQRUnipotentMatrix_entry]
  have hr : Continuous (fun g : (L →L[ℝ] L)ˣ => operatorQRTriangularMatrix b g i) :=
    (continuous_apply i).comp (operatorQRTriangularMatrix_continuous b)
  have he : Continuous (fun g : (L →L[ℝ] L)ˣ => operatorQRTriangularMatrix b g i j) :=
    (continuous_apply j).comp hr
  exact ((OperatorQRBasis.Construction.operatorQRDiagonal_continuous b i).inv₀ (fun g => ne_of_gt (OperatorQRBasis.Construction.operatorQRDiagonal_pos b g i))).mul
    he

end

section

/-! The logarithmic diagonal and the unipotent QR factor are
continuous coordinates, including the topology of the unipotent group. -/

open scoped Classical _root_.Matrix.Norms.Operator

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def operatorQRLogDiagonal {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : (L →L[ℝ] L)ˣ) (i : Fin m) : ℝ := Real.log (OperatorQRBasis.Construction.operatorQRDiagonal b g i)

omit [FiniteDimensional ℝ L] in
theorem operatorQRLogDiagonal_continuous {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) :
    Continuous (operatorQRLogDiagonal b) := by
  apply continuous_pi
  intro i
  exact (OperatorQRBasis.Construction.operatorQRDiagonal_continuous b i).log (fun g => ne_of_gt (OperatorQRBasis.Construction.operatorQRDiagonal_pos b g i))

def operatorQRUnipotentUnit {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (g : (L →L[ℝ] L)ˣ) :
    (Matrix (Fin m) (Fin m) ℝ)ˣ := (operatorQRUnipotentMatrix_unitriangular b g).isUnit.unit

theorem operatorQRUnipotentUnit_val {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (g : (L →L[ℝ] L)ˣ) :
    (operatorQRUnipotentUnit b g).val = operatorQRUnipotentMatrix b g :=
  (operatorQRUnipotentMatrix_unitriangular b g).isUnit.unit_spec

theorem operatorQRUnipotentUnit_continuous {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) :
    Continuous (operatorQRUnipotentUnit b) := by
  apply Units.isOpenEmbedding_val.isEmbedding.continuous_iff.mpr
  change Continuous (fun g => (operatorQRUnipotentUnit b g).val)
  simp_rw [operatorQRUnipotentUnit_val]
  exact operatorQRUnipotentMatrix_continuous b

end

/-! Logarithmic and unipotent QR coordinates depend only on the
ordered input frame, so orthonormal basis changes become fixed right translations. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem operatorQR_same_frame {m : ℕ} (b c : OrthonormalBasis (Fin m) ℝ L)
    (g h : (L →L[ℝ] L)ˣ) (hf : ∀ i, g.val (b i) = h.val (c i)) :
    operatorQRLogDiagonal b g = operatorQRLogDiagonal c h ∧
      operatorQRUnipotentMatrix b g = operatorQRUnipotentMatrix c h := by
  have he : (fun i => g.val (b i)) = (fun i => h.val (c i)) := funext hf
  have hd : OperatorQRBasis.Construction.operatorQRDiagonal b g = OperatorQRBasis.Construction.operatorQRDiagonal c h := by
    unfold OperatorQRBasis.Construction.operatorQRDiagonal
    rw [he]
  have hB : OperatorQRBasis.Construction.operatorQRBasis b g = OperatorQRBasis.Construction.operatorQRBasis c h := by
    unfold OperatorQRBasis.Construction.operatorQRBasis
    rw [he]
  have hR : operatorQRTriangularMatrix b g = operatorQRTriangularMatrix c h := by
    ext i j
    rw [operatorQRTriangularMatrix_entry, operatorQRTriangularMatrix_entry, hB, hf j]
  constructor
  · funext i
    unfold operatorQRLogDiagonal
    rw [hd]
  · unfold operatorQRUnipotentMatrix
    rw [hd, hR]

def orthonormalBasisChangeUnit {m : ℕ} (b c : OrthonormalBasis (Fin m) ℝ L) : (L →L[ℝ] L)ˣ :=
  (b.equiv c (Equiv.refl _)).toContinuousLinearEquiv.toUnit

omit [FiniteDimensional ℝ L] in
theorem orthonormalBasisChangeUnit_apply {m : ℕ} (b c : OrthonormalBasis (Fin m) ℝ L) (i : Fin m) :
    (orthonormalBasisChangeUnit b c).val (b i) = c i := b.equiv_apply_basis c (Equiv.refl _) i

theorem operatorQR_basis_change {m : ℕ} (b c : OrthonormalBasis (Fin m) ℝ L) (g : (L →L[ℝ] L)ˣ) :
    operatorQRLogDiagonal c g = operatorQRLogDiagonal b (g * orthonormalBasisChangeUnit b c) ∧
      operatorQRUnipotentMatrix c g = operatorQRUnipotentMatrix b (g * orthonormalBasisChangeUnit b c) := by
  apply operatorQR_same_frame c b g (g * orthonormalBasisChangeUnit b c)
  intro i
  change g.val (c i) = g.val ((orthonormalBasisChangeUnit b c).val (b i))
  rw [orthonormalBasisChangeUnit_apply]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRVal.Construction
