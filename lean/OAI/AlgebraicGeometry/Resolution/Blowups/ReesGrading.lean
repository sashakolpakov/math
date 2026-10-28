import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-! # Rees Grading -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ReesGrading.Construction

/-! The natural grading on the actual Rees algebra, for the blowup construction
needed in Blowups. No resolution existence assertion is assumed in this file. -/

open _root_.Polynomial DirectSum _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R]

/-- The degree-`n` part of `R[It]` consists of polynomials supported in degree `n`. -/
def reesGrade (I : Ideal R) (n : ℕ) : Submodule R (reesAlgebra I) where
  carrier := {p | ∀ m, m ≠ n → (p : R[X]).coeff m = 0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq m hm
    change (p.val + q.val).coeff m = 0
    simp [hp m hm, hq m hm]
  smul_mem' := by
    intro r p hp m hm
    change (r • p.val).coeff m = 0
    simp [hp m hm]

theorem reesGrade_eq_monomial (I : Ideal R) (n : ℕ)
    (p : reesAlgebra I) (hp : p ∈ reesGrade I n) :
    (p : R[X]) = monomial n ((p : R[X]).coeff n) := by
  ext m
  by_cases hm : m = n
  · subst m
    simp
  · simp [coeff_monomial, Ne.symm hm, hp m hm]

theorem monomial_mem_reesGrade (I : Ideal R) (n : ℕ)
    (r : R) (hr : r ∈ I ^ n) :
    (⟨monomial n r, reesAlgebra.monomial_mem.mpr hr⟩ : reesAlgebra I)
      ∈ reesGrade I n := by
  intro m hm
  simp [coeff_monomial, Ne.symm hm]

instance reesGrade_gradedMonoid (I : Ideal R) : SetLike.GradedMonoid (reesGrade I) where
  one_mem := by
    intro m hm
    simp [coeff_one, hm]
  mul_mem := by
    intro i j p q hp hq m hm
    change (p.val * q.val).coeff m = 0
    rw [reesGrade_eq_monomial I i p hp, reesGrade_eq_monomial I j q hq]
    simp [monomial_mul_monomial, coeff_monomial, Ne.symm hm]

theorem rees_recompose_coeff (I : Ideal R)
    (p : ⨁ n, reesGrade I n) (n : ℕ) :
    (((DirectSum.coeAddMonoidHom (reesGrade I)) p : reesAlgebra I) : R[X]).coeff n =
      (((p n : reesGrade I n) : reesAlgebra I) : R[X]).coeff n := by
  induction p using DirectSum.induction_on with
  | zero => simp
  | of j p =>
    by_cases h : j = n
    · subst j
      simp
    · simp [DirectSum.of_eq_of_ne (β := fun n => reesGrade I n) j n p (Ne.symm h),
        p.property n (Ne.symm h)]
  | add p q hp hq => simp_all

theorem reesGrade_isInternal (I : Ideal R) : DirectSum.IsInternal (reesGrade I) := by
  classical
  constructor
  · intro p q hpq
    apply DFinsupp.ext
    intro n
    apply Subtype.ext
    apply Subtype.ext
    rw [reesGrade_eq_monomial I n (p n) (p n).property,
      reesGrade_eq_monomial I n (q n) (q n).property]
    congr 1
    rw [← rees_recompose_coeff I p n, ← rees_recompose_coeff I q n, hpq]
  · intro p
    let piece (n : ℕ) : reesGrade I n :=
      ⟨⟨monomial n (p.val.coeff n), reesAlgebra.monomial_mem.mpr (p.property n)⟩,
        monomial_mem_reesGrade I n _ (p.property n)⟩
    refine ⟨∑ n ∈ p.val.support, DirectSum.of (fun n => reesGrade I n) n (piece n), ?_⟩
    apply Subtype.ext
    simpa [piece] using p.val.as_sum_support.symm

noncomputable instance reesGrade_gradedAlgebra (I : Ideal R) :
    GradedAlgebra (reesGrade I) :=
  (reesGrade_isInternal I).gradedAlgebra

/-- The degree-zero part of the Rees algebra is exactly the original ring. -/
theorem reesGrade_zero_algebraMap_surjective (I : Ideal R) :
    Function.Surjective (algebraMap R (reesGrade I 0)) := by
  intro p
  refine ⟨((p : reesAlgebra I) : R[X]).coeff 0, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  simpa using (reesGrade_eq_monomial I 0 p.val p.property).symm

instance reesGrade_zero_scalarTower (I : Ideal R) :
    IsScalarTower R (reesGrade I 0) (reesAlgebra I) :=
  IsScalarTower.of_algebraMap_eq' (R := R) (S := reesGrade I 0) (A := reesAlgebra I) rfl

instance reesGrade_zero_finiteType (I : Ideal R) [IsNoetherianRing R] :
    Algebra.FiniteType (reesGrade I 0) (reesAlgebra I) :=
  Algebra.FiniteType.of_restrictScalars_finiteType R (reesGrade I 0) (reesAlgebra I)

/-- The affine blowup as the projective spectrum of the actual Rees algebra. -/
noncomputable abbrev affineBlowup (I : Ideal R) : Scheme := Proj (reesGrade I)

/-- The structural morphism of the affine blowup. -/
noncomputable def affineBlowupToSpec (I : Ideal R) : affineBlowup I ⟶ Spec (.of R) :=
  Proj.toSpecZero (reesGrade I) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (reesGrade I 0)))

/-- Blowup of an affine Noetherian scheme is proper over that scheme. -/
instance affineBlowupToSpec_isProper (I : Ideal R) [IsNoetherianRing R] :
    IsProper (affineBlowupToSpec I) := by
  let φ : R →+* reesGrade I 0 := algebraMap R (reesGrade I 0)
  have hφ : Function.Surjective φ := reesGrade_zero_algebraMap_surjective I
  let φcat : CommRingCat.of R ⟶ CommRingCat.of (reesGrade I 0) := CommRingCat.ofHom φ
  have hφcat : Function.Surjective φcat := hφ
  let : IsClosedImmersion (Spec.map φcat) :=
    IsClosedImmersion.spec_of_surjective φcat hφcat
  change IsProper (Proj.toSpecZero (reesGrade I) ≫ Spec.map (CommRingCat.ofHom φ))
  infer_instance

end OAI.AlgebraicGeometry.Resolution.Blowups.ReesGrading.Construction
