import OAI.NumberTheory.Quaternion.Arithmetic.ConjugationQuaternion
import OAI.NumberTheory.Quaternion.Arithmetic.MatrixDetFour

/-! # Matrix Quaternion Det -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.MatrixQuaternionDet

noncomputable section

section

/-! The faithful four-dimensional regular representation of a
quaternion algebra and its determinant, the square of the reduced norm. -/

open scoped Classical _root_.Quaternion _root_.Matrix
open QuaternionAlgebra _root_.Matrix

variable {K : Type*} [Field K] (a b : K)

def quaternionRegularMatrix : ℍ[K,a,b] →ₐ[K] Matrix (Fin 4) (Fin 4) K :=
  Algebra.leftMulMatrix (basisOneIJK a 0 b)

theorem quaternionRegularMatrix_injective : Function.Injective (quaternionRegularMatrix a b) :=
  Algebra.leftMulMatrix_injective _

theorem quaternionRegularMatrix_apply (q : ℍ[K,a,b]) :
    quaternionRegularMatrix a b q =
      !![q.re, a * q.imI, b * q.imJ, -a * b * q.imK;
         q.imI, q.re, b * q.imK, -b * q.imJ;
         q.imJ, -a * q.imK, q.re, a * q.imI;
         q.imK, -q.imJ, q.imI, q.re] := by
  ext i j
  change Algebra.leftMulMatrix (basisOneIJK a 0 b) q i j = _
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  change (![ (q * basisOneIJK a 0 b j).re, (q * basisOneIJK a 0 b j).imI,
    (q * basisOneIJK a 0 b j).imJ, (q * basisOneIJK a 0 b j).imK ]) i = _
  simp only [basisOneIJK, Module.Basis.coe_ofEquivFun,
    coe_linearEquivTuple_symm, equivTuple_symm_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val_two, Matrix.cons_val_three]

theorem quaternionRegularMatrix_det (q : ℍ[K,a,b]) :
    (quaternionRegularMatrix a b q).det = Norm.quaternionNorm a b q ^ 2 := by
  rw [quaternionRegularMatrix_apply, MatrixDetFour.matrix_det_four_expand, Norm.quaternionNorm_formula]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.cons_val_three]
  ring

theorem quaternionRegularMatrix_firstColumn (q : ℍ[K,a,b]) :
    QuaternionAlgebra.mk (quaternionRegularMatrix a b q 0 0) (quaternionRegularMatrix a b q 1 0)
      (quaternionRegularMatrix a b q 2 0) (quaternionRegularMatrix a b q 3 0) = q := by
  rw [quaternionRegularMatrix_apply]
  rfl

end

section

/-! The faithful regular representation realizes quaternion norm-one
units as a subgroup of SL₄. -/

open scoped Classical _root_.Quaternion
open QuaternionAlgebra _root_.Matrix

variable {K : Type*} [Field K] (a b : K)

def quaternionRegularNormOneHom : (Norm.quaternionUnitNorm a b).ker →* Matrix.SpecialLinearGroup (Fin 4) K where
  toFun q := ⟨quaternionRegularMatrix a b q.val.val, by
    rw [quaternionRegularMatrix_det]
    have hn : Norm.quaternionNorm a b q.val.val = 1 := congrArg Units.val (MonoidHom.mem_ker.mp q.property)
    rw [hn, one_pow]⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (quaternionRegularMatrix a b)
  map_mul' q r := by
    apply Subtype.ext
    exact map_mul (quaternionRegularMatrix a b) q.val.val r.val.val

theorem quaternionRegularNormOneHom_injective : Function.Injective (quaternionRegularNormOneHom a b) := by
  intro q r h
  apply Subtype.ext
  apply Units.ext
  apply quaternionRegularMatrix_injective a b
  exact congrArg Subtype.val h

theorem quaternionRegularNormOneHom_mem_range (M : Matrix.SpecialLinearGroup (Fin 4) K) :
    M ∈ (quaternionRegularNormOneHom a b).range ↔
      ∃ q : ℍ[K,a,b], Norm.quaternionNorm a b q = 1 ∧ quaternionRegularMatrix a b q = M.val := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.val.val, congrArg Units.val (MonoidHom.mem_ker.mp q.property), rfl⟩
  · rintro ⟨q, hn, hq⟩
    let u := Norm.quaternionUnitOfNormNeZero a b q (by rw [hn]; exact one_ne_zero)
    have hu : u ∈ (Norm.quaternionUnitNorm a b).ker := by
      apply MonoidHom.mem_ker.mpr
      apply Units.ext
      exact hn
    refine ⟨⟨u, hu⟩, ?_⟩
    exact Subtype.ext hq

end

/-! Polynomial equations for the regular quaternion representation
and its reduced-norm-one subgroup. -/

open scoped Classical _root_.Quaternion _root_.Matrix
open QuaternionAlgebra _root_.Matrix

variable {F K : Type} [Field F] [Field K]

def quaternionFirstColumn (a b : K) (M : Matrix (Fin 4) (Fin 4) K) : ℍ[K,a,b] :=
  ⟨M 0 0, M 1 0, M 2 0, M 3 0⟩

def quaternionLinearPolynomials (a b : F) : Matrix (Fin 4) (Fin 4) (ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial 4 F) :=
  let r : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial 4 F := MvPolynomial.X (0, 0)
  let s : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial 4 F := MvPolynomial.X (1, 0)
  let t : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial 4 F := MvPolynomial.X (2, 0)
  let u : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial 4 F := MvPolynomial.X (3, 0)
  !![r, MvPolynomial.C a * s, MvPolynomial.C b * t, -MvPolynomial.C a * MvPolynomial.C b * u;
     s, r, MvPolynomial.C b * u, -MvPolynomial.C b * t;
     t, -MvPolynomial.C a * u, r, MvPolynomial.C a * s;
     u, -t, s, r]

def quaternionNormEquation (a b : F) : ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial 4 F :=
  MvPolynomial.X (0, 0) ^ 2 - MvPolynomial.C a * MvPolynomial.X (1, 0) ^ 2 -
    MvPolynomial.C b * MvPolynomial.X (2, 0) ^ 2 +
    MvPolynomial.C a * MvPolynomial.C b * MvPolynomial.X (3, 0) ^ 2 - 1

def quaternionMatrixEquations (a b : F) : Set (ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial 4 F) :=
  Set.range (fun ij : Fin 4 × Fin 4 => MvPolynomial.X ij - quaternionLinearPolynomials a b ij.1 ij.2) ∪
    {quaternionNormEquation a b}

theorem quaternionLinearPolynomials_eval (ρ : F →+* K) (a b : F) (M : Matrix (Fin 4) (Fin 4) K) :
    (quaternionLinearPolynomials a b).map (MvPolynomial.eval₂Hom ρ (fun ij => M ij.1 ij.2)) =
      quaternionRegularMatrix (ρ a) (ρ b) (quaternionFirstColumn (ρ a) (ρ b) M) := by
  rw [quaternionRegularMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionLinearPolynomials, quaternionFirstColumn, Matrix.map_apply,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem quaternionNormEquation_eval (ρ : F →+* K) (a b : F) (M : Matrix (Fin 4) (Fin 4) K) :
    MvPolynomial.eval₂Hom ρ (fun ij => M ij.1 ij.2) (quaternionNormEquation a b) =
      Norm.quaternionNorm (ρ a) (ρ b) (quaternionFirstColumn (ρ a) (ρ b) M) - 1 := by
  simp [quaternionNormEquation, quaternionFirstColumn, Norm.quaternionNorm_formula]

theorem quaternionMatrixEquations_iff (ρ : F →+* K) (a b : F)
    (M : Matrix.SpecialLinearGroup (Fin 4) K) :
    (∀ p ∈ quaternionMatrixEquations a b, ArithmeticGroups.Lattices.Algebraic.evaluateMatrix ρ M p = 0) ↔
      quaternionRegularMatrix (ρ a) (ρ b) (quaternionFirstColumn (ρ a) (ρ b) M.val) = M.val ∧
        Norm.quaternionNorm (ρ a) (ρ b) (quaternionFirstColumn (ρ a) (ρ b) M.val) = 1 := by
  let ev := ArithmeticGroups.Lattices.Algebraic.evaluateMatrix ρ M
  have hX (ij : Fin 4 × Fin 4) : ev (MvPolynomial.X ij) = M.val ij.1 ij.2 := by
    simp [ev, ArithmeticGroups.Lattices.Algebraic.evaluateMatrix]
  have he (i j : Fin 4) : ev (quaternionLinearPolynomials a b i j) =
      quaternionRegularMatrix (ρ a) (ρ b) (quaternionFirstColumn (ρ a) (ρ b) M.val) i j :=
    congrFun (congrFun (quaternionLinearPolynomials_eval ρ a b M.val) i) j
  have hn : ev (quaternionNormEquation a b) =
      Norm.quaternionNorm (ρ a) (ρ b) (quaternionFirstColumn (ρ a) (ρ b) M.val) - 1 :=
    quaternionNormEquation_eval ρ a b M.val
  constructor
  · intro h
    constructor
    · apply Matrix.ext
      intro i j
      have hi := h (MvPolynomial.X (i, j) - quaternionLinearPolynomials a b i j)
        (Or.inl (Set.mem_range_self (i, j)))
      change ev (MvPolynomial.X (i, j) - quaternionLinearPolynomials a b i j) = 0 at hi
      rw [map_sub, hX, he] at hi
      exact (sub_eq_zero.mp hi).symm
    · exact sub_eq_zero.mp (hn.symm.trans (h _ (Or.inr (Set.mem_singleton _))))
  · rintro ⟨hM, hnorm⟩ p (⟨ij, rfl⟩ | rfl)
    · change ev (MvPolynomial.X ij - quaternionLinearPolynomials a b ij.1 ij.2) = 0
      rw [map_sub, hX, he, hM]
      exact sub_self _
    · exact hn.trans (sub_eq_zero.mpr hnorm)

end

end OAI.NumberTheory.Quaternion.Arithmetic.MatrixQuaternionDet
