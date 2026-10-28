import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearChart

/-! # Projective Linear -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveLinear

noncomputable section

/-! Invertible matrices over an arbitrary coefficient ring act on
the actual relative projective spectrum of the polynomial ring. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

abbrev grading (R : Type) [CommRing R] (n : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

instance gradedAlgebra (R : Type) [CommRing R] (n : ℕ) : GradedAlgebra (grading R n) :=
  MvPolynomial.gradedAlgebra

abbrev space (R : Type) [CommRing R] (n : ℕ) : Scheme := Proj (grading R n)

variable {R : Type} [CommRing R]

def form {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (i : Fin (m + 1)) : MvPolynomial (Fin (n + 1)) R :=
  ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j

theorem form_homogeneous {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (i : Fin (m + 1)) : MvPolynomial.IsHomogeneous (form A i) 1 :=
  MvPolynomial.IsHomogeneous.sum _ _ _ (fun j _ => MvPolynomial.isHomogeneous_C_mul_X (A i j) j)

def algebraHom {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) R) :
    MvPolynomial (Fin (m + 1)) R →ₐ[R] MvPolynomial (Fin (n + 1)) R := MvPolynomial.aeval (form A)

theorem algebraHom_X {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (i : Fin (m + 1)) : algebraHom A (MvPolynomial.X i) = form A i := MvPolynomial.aeval_X _ _

theorem algebraHom_C {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (r : R) : algebraHom A (MvPolynomial.C r) = MvPolynomial.C r := MvPolynomial.aeval_C _ _

def gradedHom {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) R) : grading R m →+*ᵍ grading R n where
  __ := (algebraHom A).toRingHom
  map_mem {d} {p} hp := by
    change MvPolynomial.IsHomogeneous (MvPolynomial.aeval (form A) p) d
    rw [MvPolynomial.aeval_def]
    simpa only [one_mul, MvPolynomial.algebraMap_eq] using MvPolynomial.IsHomogeneous.eval₂ hp
      (MvPolynomial.C : R →+* MvPolynomial (Fin (n + 1)) R) (form A)
      (MvPolynomial.isHomogeneous_C _) (form_homogeneous A)

theorem form_one (n : ℕ) (i : Fin (n + 1)) :
    form (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i = MvPolynomial.X i := by
  classical
  simp [form, Matrix.one_apply]

theorem algebraHom_one (n : ℕ) : algebraHom (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
    AlgHom.id R (MvPolynomial (Fin (n + 1)) R) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [algebraHom_X, form_one, AlgHom.id_apply]

theorem algebraHom_form {l m n : ℕ}
    (A : Matrix (Fin (l + 1)) (Fin (m + 1)) R)
    (B : Matrix (Fin (m + 1)) (Fin (n + 1)) R) (i : Fin (l + 1)) :
    algebraHom B (form A i) = form (A * B) i := by
  simp only [form, map_sum, map_mul, algebraHom_C, algebraHom_X, Matrix.mul_apply]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

theorem gradedHom_one (n : ℕ) : gradedHom (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
    GradedRingHom.id (grading R n) := by
  apply GradedRingHom.ext
  intro p
  change algebraHom _ p = p
  rw [algebraHom_one, AlgHom.id_apply]

theorem gradedHom_mul {l m n : ℕ}
    (A : Matrix (Fin (l + 1)) (Fin (m + 1)) R)
    (B : Matrix (Fin (m + 1)) (Fin (n + 1)) R) :
    gradedHom (A * B) = (gradedHom B).comp (gradedHom A) := by
  have he : algebraHom (A * B) = (algebraHom B).comp (algebraHom A) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [algebraHom_X, AlgHom.comp_apply]
    exact (algebraHom_form A B i).symm
  apply GradedRingHom.ext
  intro p
  exact DFunLike.congr_fun he p

variable {n : ℕ} (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) R)ˣ)

theorem irrelevant_le : HomogeneousIdeal.irrelevant (grading R n) ≤
    (HomogeneousIdeal.irrelevant (grading R n)).map (gradedHom A.val) := by
  apply (HomogeneousIdeal.irrelevant_le (grading R n)).mpr
  intro d hd p hp
  have hq : gradedHom A.inv p ∈ HomogeneousIdeal.irrelevant (grading R n) :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ hd ((gradedHom A.inv).map_mem hp)
  have hi : (gradedHom A.val).comp (gradedHom A.inv) = GradedRingHom.id (grading R n) := by
    rw [← gradedHom_mul, A.inv_val, gradedHom_one]
  have he : gradedHom A.val (gradedHom A.inv p) = p := DFunLike.congr_fun hi p
  exact he ▸ Ideal.mem_map_of_mem (gradedHom A.val).toRingHom hq

def map : space R n ⟶ space R n := Proj.map (gradedHom A.val) (ProjectiveLinear.irrelevant_le A)

theorem map_one : ProjectiveLinear.map (1 : (Matrix (Fin (n + 1)) (Fin (n + 1)) R)ˣ) = 𝟙 (space R n) := by
  unfold ProjectiveLinear.map
  simp only [Units.val_one, gradedHom_one, Proj.map_id]

theorem map_mul (B : (Matrix (Fin (n + 1)) (Fin (n + 1)) R)ˣ) : ProjectiveLinear.map (A * B) = ProjectiveLinear.map B ≫ ProjectiveLinear.map A := by
  unfold ProjectiveLinear.map
  simp only [Units.val_mul, gradedHom_mul]
  exact Proj.map_comp (gradedHom A.val) (gradedHom B.val) (ProjectiveLinear.irrelevant_le A) (ProjectiveLinear.irrelevant_le B)

def iso : space R n ≅ space R n where
  hom := ProjectiveLinear.map A
  inv := ProjectiveLinear.map A⁻¹
  hom_inv_id := by rw [← ProjectiveLinear.map_mul, inv_mul_cancel, map_one]
  inv_hom_id := by rw [← ProjectiveLinear.map_mul, mul_inv_cancel, map_one]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveLinear
