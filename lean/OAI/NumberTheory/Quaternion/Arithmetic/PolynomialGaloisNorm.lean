import OAI.NumberTheory.Quaternion.Arithmetic.GaloisNorm
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Polynomial Galois Norm -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.PolynomialGaloisNorm

noncomputable section

/-! Points polynomial in one base-field matrix have commuting Galois
conjugates, so their Galois norms descend to rational group points. -/

open scoped Classical
open _root_.Matrix

variable {F K : Type} [Field F] [Field K] {n : ℕ}

def matrixPointsHom (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K) :
    G.Points ι →* Matrix (Fin n) (Fin n) K where
  toFun g := g.val.val
  map_one' := rfl
  map_mul' _ _ := rfl

theorem matrixPointsHom_injective (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K) :
    Function.Injective (matrixPointsHom G ι) := by
  intro a b hab
  apply Subtype.ext
  exact Subtype.ext hab

theorem aeval_matrix_coefficientMap (ι : F →+* K)
    (A : Matrix (Fin n) (Fin n) F) (p : Polynomial F) :
    (Polynomial.aeval A p).map ι = Polynomial.aeval (A.map ι) (p.map ι) := by
  apply Polynomial.map_aeval_eq_aeval_map
    (ψ := (ι.mapMatrix : Matrix (Fin n) (Fin n) F →+* Matrix (Fin n) (Fin n) K)) (φ := ι)
  ext c i j : 2
  simp [Matrix.algebraMap_matrix_apply, Matrix.map_apply, apply_ite ι]

variable [Algebra F K]

theorem galois_point_polynomial_image (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Matrix (Fin n) (Fin n) F) (g : G.Points (algebraMap F K)) (p : Polynomial K)
    (hp : Polynomial.aeval (S.map (algebraMap F K)) p = matrixPointsHom G (algebraMap F K) g)
    (σ : K ≃ₐ[F] K) :
    matrixPointsHom G (algebraMap F K) (GaloisPoints.galoisPointsHom G σ g) =
      Polynomial.aeval (S.map (algebraMap F K)) (p.map σ.toRingHom) := by
  have hS : (S.map (algebraMap F K)).map σ = S.map (algebraMap F K) := by
    ext i j
    exact σ.commutes (S i j)
  calc
    matrixPointsHom G (algebraMap F K) (GaloisPoints.galoisPointsHom G σ g) =
        (matrixPointsHom G (algebraMap F K) g).map σ := rfl
    _ = (Polynomial.aeval (S.map (algebraMap F K)) p).map σ := congrArg (fun M => M.map σ) hp.symm
    _ = Polynomial.aeval ((S.map (algebraMap F K)).map σ) (p.map σ.toRingHom) :=
      aeval_matrix_coefficientMap σ.toRingHom (S.map (algebraMap F K)) p
    _ = Polynomial.aeval (S.map (algebraMap F K)) (p.map σ.toRingHom) :=
      congrArg (fun M => Polynomial.aeval M (p.map σ.toRingHom)) hS

theorem galois_orbit_commute_of_polynomial (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Matrix (Fin n) (Fin n) F) (g : G.Points (algebraMap F K)) (p : Polynomial K)
    (hp : Polynomial.aeval (S.map (algebraMap F K)) p = matrixPointsHom G (algebraMap F K) g) :
    ∀ σ τ : K ≃ₐ[F] K, Commute (GaloisPoints.galoisPointsHom G σ g) (GaloisPoints.galoisPointsHom G τ g) := by
  intro σ τ
  apply Commute.of_map (matrixPointsHom_injective G (algebraMap F K))
  rw [galois_point_polynomial_image G S g p hp σ, galois_point_polynomial_image G S g p hp τ]
  exact (Commute.all (p.map σ.toRingHom) (p.map τ.toRingHom)).map
    (Polynomial.aeval (S.map (algebraMap F K)))

theorem polynomial_galois_norm_descends [FiniteDimensional F K] [IsGalois F K]
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Matrix (Fin n) (Fin n) F)
    (g : G.Points (algebraMap F K)) (p : Polynomial K)
    (hp : Polynomial.aeval (S.map (algebraMap F K)) p = matrixPointsHom G (algebraMap F K) g) :
    ∃ a : G.RationalPoints, G.map (RingHom.id F) (algebraMap F K) a =
      GaloisNorm.galoisPointNorm G g (galois_orbit_commute_of_polynomial G S g p hp) :=
  GaloisNorm.galoisPointNorm_descends G g _

end

end OAI.NumberTheory.Quaternion.Arithmetic.PolynomialGaloisNorm
