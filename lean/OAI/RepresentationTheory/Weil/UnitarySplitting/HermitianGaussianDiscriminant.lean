import OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianDiagonal
import OAI.RepresentationTheory.Weil.UnitarySplitting.TensorUnitary

/-! # Hermitian Gaussian Discriminant -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianGaussianDiscriminant.Construction

noncomputable section

section

/-! Diagonalization of the actual Hermitian matrices over the base field. -/

open _root_.Matrix _root_.Module
open scoped BigOperators

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {I : Type} [Fintype I] [DecidableEq I]
variable (σ : E ≃ₐ[F] E)

def hermitianMatrixForm (A : Matrix I I E) :
    (I → E) →ₛₗ[σ.toRingHom] (I → E) →ₗ[E] E :=
  Matrix.toLinearMapₛₗ₂' E σ.toRingHom (RingHom.id E) A

theorem hermitianMatrixForm_apply (A : Matrix I I E) (x y : I → E) :
    hermitianMatrixForm σ A x y = DualPair.Construction.sesquilinear σ A x y := by
  rw [hermitianMatrixForm, Matrix.toLinearMapₛₗ₂'_apply]
  simp only [RingHom.id_apply, smul_eq_mul, DualPair.Construction.sesquilinear, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change σ (x i) * (y j * A i j) = σ (x i) * (A i j * y j)
  ring

theorem hermitianMatrixForm_symm (hσ : Function.Involutive σ)
    (A : Matrix I I E) (hA : DualPair.Construction.adjointMatrix σ A = A) : (hermitianMatrixForm σ A).IsSymm := by
  constructor
  intro x y
  rw [hermitianMatrixForm_apply, hermitianMatrixForm_apply]
  exact (TracePairing.Construction.conjugate_sesquilinear σ hσ A y x).trans (congrArg (fun L => DualPair.Construction.sesquilinear σ L y x) hA)

theorem sesquilinear_single (A : Matrix I I E) (i j : I) :
    DualPair.Construction.sesquilinear σ A (Pi.single i 1) (Pi.single j 1) = A i j := by
  rw [← hermitianMatrixForm_apply]
  exact Matrix.toLinearMap₂'Aux_single σ.toRingHom (RingHom.id E) A i j

theorem hermitian_matrix_diagonal [FiniteDimensional F E] [CharZero F]
    (hQuadratic : Module.finrank F E = 2) (hne : ∃ z : E, σ z ≠ z)
    {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (hA : DualPair.Construction.adjointMatrix σ A = A) (hdet : A.det ≠ 0) :
    ∃ u : (Matrix (Fin n) (Fin n) E)ˣ, ∃ a : Fin n → F,
      (∀ i, a i ≠ 0) ∧
      DualPair.Construction.adjointMatrix σ (u : Matrix (Fin n) (Fin n) E) * A * (u : Matrix (Fin n) (Fin n) E) =
        Matrix.diagonal (fun i => algebraMap F E (a i)) := by
  let B := hermitianMatrixForm σ A
  have hsym := hermitianMatrixForm_symm σ (TracePairing.Construction.quadratic_automorphism_involutive hQuadratic σ) A hA
  have hex := HermitianDiagonal.Construction.hermitian_orthogonal_basis σ.toRingHom B hne hsym
  have hdim : Module.finrank E (Fin n → E) = n := by
    exact (Module.finrank_pi E).trans (Fintype.card_fin n)
  have hex' : ∃ b : Basis (Fin n) E (Fin n → E), B.IsOrthoᵢ b := by
    rw [hdim] at hex
    exact hex
  obtain ⟨b, hb⟩ := hex'
  let e := Pi.basisFun E (Fin n)
  let u : (Matrix (Fin n) (Fin n) E)ˣ :=
    ⟨e.toMatrix b, b.toMatrix e, e.toMatrix_mul_toMatrix_flip b, b.toMatrix_mul_toMatrix_flip e⟩
  have hcol (i : Fin n) : (u : Matrix (Fin n) (Fin n) E).col i = b i := by
    ext j
    change e.repr (b i) j = b i j
    simp [e]
  have hentry (i j : Fin n) :
      (DualPair.Construction.adjointMatrix σ (u : Matrix (Fin n) (Fin n) E) * A * (u : Matrix (Fin n) (Fin n) E)) i j =
        B (b i) (b j) := by
    rw [← sesquilinear_single σ
      (DualPair.Construction.adjointMatrix σ (u : Matrix (Fin n) (Fin n) E) * A * (u : Matrix (Fin n) (Fin n) E)) i j,
      ← DualPair.Construction.sesquilinear_change]
    rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one, hcol, hcol]
    exact (hermitianMatrixForm_apply σ A (b i) (b j)).symm
  have hd : DualPair.Construction.adjointMatrix σ (u : Matrix (Fin n) (Fin n) E) * A * (u : Matrix (Fin n) (Fin n) E) =
      Matrix.diagonal (fun i => B (b i) (b i)) := by
    ext i j
    rw [hentry, Matrix.diagonal_apply]
    by_cases hij : i = j
    · simp [hij]
    · rw [ite_eq_right hij]
      exact hb hij
  have hnonzero : ∀ i, B (b i) (b i) ≠ 0 := by
    have hul : (u : Matrix (Fin n) (Fin n) E).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp u.isUnit).ne_zero
    have hr : (∏ i, B (b i) (b i)) ≠ 0 := by
      rw [← Matrix.det_diagonal, ← hd, Matrix.det_mul, Matrix.det_mul, TracePairing.Construction.adjointMatrix_det]
      exact mul_ne_zero (mul_ne_zero ((map_ne_zero σ).mpr hul) hdet) hul
    exact fun i => (Finset.prod_ne_zero_iff.mp hr) i (Finset.mem_univ i)
  have hbase (i : Fin n) : ∃ a : F, algebraMap F E a = B (b i) (b i) :=
    (QuadraticNorm.Construction.quadratic_fixed_iff hQuadratic σ hne _).mp (hsym.eq (b i) (b i))
  choose a ha using hbase
  refine ⟨u, a, ?_, ?_⟩
  · intro i hai
    apply hnonzero i
    rw [← ha i, hai, map_zero]
  · rw [hd]
    congr 1
    exact funext fun i => (ha i).symm

end

/-! The quadratic character of a Hermitian determinant is unchanged by
the norm factor in diagonalization. -/

open _root_.Matrix
open scoped BigOperators

theorem hermitianDiagonal_discriminant_character
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [FiniteDimensional F E] [CharZero F]
    (hQuadratic : Module.finrank F E = 2) (σ : E ≃ₐ[F] E) (hne : ∃ z : E, σ z ≠ z)
    (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
    {d : ℕ} (A : Matrix (Fin d) (Fin d) E) (u : (Matrix (Fin d) (Fin d) E)ˣ)
    (a : Fin d → Fˣ) (b : Fˣ) (hb : algebraMap F E (b : F) = A.det)
    (hdiag : DualPair.Construction.adjointMatrix σ (u : Matrix (Fin d) (Fin d) E) * A *
      (u : Matrix (Fin d) (Fin d) E) = Matrix.diagonal (fun i => algebraMap F E (a i : F))) :
    ω (∏ i, a i) = ω b := by
  let t := TensorUnitary.Construction.matrixDetUnit u
  have heq : (∏ i, a i) = b * Units.map (Algebra.norm F) t := by
    apply Units.ext
    apply (algebraMap F E).injective
    have hh := congrArg Matrix.det hdiag
    rw [Matrix.det_mul, Matrix.det_mul, TracePairing.Construction.adjointMatrix_det, Matrix.det_diagonal] at hh
    change algebraMap F E (↑(∏ i, a i) : F) =
      algebraMap F E ((b : F) * Algebra.norm F (t : E))
    rw [map_mul, hb, QuadraticNorm.Construction.quadratic_norm_formula hQuadratic σ hne]
    have hprod : algebraMap F E (↑(∏ i, a i) : F) =
        ∏ i, algebraMap F E (a i : F) := by rw [Units.coe_prod, map_prod]
    rw [hprod, ← hh]
    change σ (u : Matrix (Fin d) (Fin d) E).det * A.det * (u : Matrix (Fin d) (Fin d) E).det =
      A.det * ((u : Matrix (Fin d) (Fin d) E).det * σ (u : Matrix (Fin d) (Fin d) E).det)
    ring
  have hnorm : ω (Units.map (Algebra.norm F) t) = 1 := (hω _).mpr ⟨t, rfl⟩
  rw [heq, map_mul, hnorm, mul_one]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianGaussianDiscriminant.Construction
