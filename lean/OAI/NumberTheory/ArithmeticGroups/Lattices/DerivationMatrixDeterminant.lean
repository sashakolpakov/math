import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Trace

/-! # Derivation Matrix Determinant -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.DerivationMatrixDeterminant.Construction

noncomputable section

/-! An algebraic derivation acts on a matrix determinant by multiplying
by the trace when its entrywise action is right multiplication. -/

open scoped Classical
open _root_.MvPolynomial

def derivationCurve {k R σ : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (D : Derivation k R R) (a : σ → R) : σ → Polynomial R :=
  fun i => Polynomial.C (a i) + Polynomial.X * Polynomial.C (D (a i))

theorem derivationCurve_eval_zero
    {k R σ : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (D : Derivation k R R) (a : σ → R) (p : MvPolynomial σ k) :
    (MvPolynomial.eval₂Hom ((Polynomial.C).comp (algebraMap k R)) (derivationCurve D a) p).eval 0 =
      MvPolynomial.eval₂Hom (algebraMap k R) a p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X', Polynomial.eval_mul, hp]
      simp [derivationCurve]

theorem derivationCurve_derivative_eval_zero
    {k R σ : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (D : Derivation k R R) (a : σ → R) (p : MvPolynomial σ k) :
    (MvPolynomial.eval₂Hom ((Polynomial.C).comp (algebraMap k R)) (derivationCurve D a) p).derivative.eval 0 =
      D (MvPolynomial.eval₂Hom (algebraMap k R) a p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, Polynomial.derivative_mul,
        Polynomial.eval_add, Polynomial.eval_mul, hp, derivationCurve_eval_zero,
        Derivation.leibniz, smul_eq_mul]
      simp [derivationCurve]
      ring

def derivationMatrixCurve {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}
    (D : Derivation k R R) (M : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) (Polynomial R) :=
  Matrix.of (fun i j => Polynomial.C (M i j) + Polynomial.X * Polynomial.C (D (M i j)))

theorem derivation_det_eq_curve_derivative
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}
    (D : Derivation k R R) (M : Matrix (Fin n) (Fin n) R) :
    D M.det = (derivationMatrixCurve D M).det.derivative.eval 0 := by
  let X : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) k) := fun i j => MvPolynomial.X (i, j)
  have h := derivationCurve_derivative_eval_zero D (fun ij : Fin n × Fin n => M ij.1 ij.2) X.det
  have h0 : (MvPolynomial.eval₂Hom (algebraMap k R) (fun ij : Fin n × Fin n => M ij.1 ij.2)).mapMatrix X = M := by
    ext i j : 1
    change (MvPolynomial.eval₂Hom (algebraMap k R) (fun ij : Fin n × Fin n => M ij.1 ij.2))
      (MvPolynomial.X (i, j)) = M i j
    rw [MvPolynomial.eval₂Hom_X']
  have h1 : (MvPolynomial.eval₂Hom ((Polynomial.C).comp (algebraMap k R))
      (derivationCurve D (fun ij : Fin n × Fin n => M ij.1 ij.2))).mapMatrix X =
      derivationMatrixCurve D M := by
    ext i j : 1
    change (MvPolynomial.eval₂Hom ((Polynomial.C).comp (algebraMap k R))
      (derivationCurve D (fun ij : Fin n × Fin n => M ij.1 ij.2)))
      (MvPolynomial.X (i, j)) = _
    rw [MvPolynomial.eval₂Hom_X']
    rfl
  rw [RingHom.map_det, RingHom.map_det, h0, h1] at h
  exact h.symm

theorem derivation_det_of_entry_eq_mul
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}
    (D : Derivation k R R) (M C : Matrix (Fin n) (Fin n) R)
    (hD : ∀ i j, D (M i j) = (M * C) i j) : D M.det = M.det * C.trace := by
  have hcurve : derivationMatrixCurve D M =
      Polynomial.C.mapMatrix M * (1 + (Polynomial.X : Polynomial R) • Polynomial.C.mapMatrix C) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      ← (Polynomial.C.mapMatrix : Matrix (Fin n) (Fin n) R →+*
        Matrix (Fin n) (Fin n) (Polynomial R)).map_mul M C]
    ext i j : 1
    change Polynomial.C (M i j) + Polynomial.X * Polynomial.C (D (M i j)) =
      Polynomial.C (M i j) + Polynomial.X * Polynomial.C ((M * C) i j)
    rw [hD]
  rw [derivation_det_eq_curve_derivative, hcurve, Matrix.det_mul, ← RingHom.map_det,
    Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.eval_mul, Polynomial.eval_C]
  exact congrArg (fun z : R => M.det * z) (Matrix.derivative_det_one_add_X_smul C)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.DerivationMatrixDeterminant.Construction
