import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveZeroLocus

/-! # Dehomogenization C -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

/-!
# Dehomogenization on standard projective charts

The substitution sends the selected homogeneous variable to one and every
other variable to its corresponding affine variable. Its evaluation is proved
to agree with the normalized coordinates of the actual projective chart. For
homogeneous equations this identifies projective vanishing with the affine
polynomial equation, rather than assuming such an identification.
-/

open _root_.MvPolynomial OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

variable {ι R K : Type*}

/-- Insert a coordinate equal to one into an affine coordinate vector. -/
noncomputable def insertOne [One R] (i : ι) (x : {j : ι // j ≠ i} → R) : ι → R := by
  classical
  exact fun j => if h : j = i then 1 else x ⟨j, h⟩

@[simp]
theorem insertOne_self [One R] (i : ι) (x : {j : ι // j ≠ i} → R) :
    insertOne i x i = 1 := by
  classical
  simp [insertOne]

@[simp]
theorem insertOne_of_ne [One R] (i j : ι) (x : {j : ι // j ≠ i} → R) (hj : j ≠ i) :
    insertOne i x j = x ⟨j, hj⟩ := by
  classical
  simp [insertOne, hj]

/-- Polynomial substitution defining the affine equation on the `i`-th patch. -/
noncomputable def dehomogenize [CommSemiring R] (i : ι) :
    MvPolynomial ι R →+* MvPolynomial {j : ι // j ≠ i} R :=
  eval₂Hom C (insertOne i X)

@[simp]
theorem dehomogenize_C [CommSemiring R] (i : ι) (r : R) :
    dehomogenize i (C r) = C r := by
  simp [dehomogenize]

@[simp]
theorem dehomogenize_X_self [CommSemiring R] (i : ι) :
    dehomogenize (R := R) i (X i) = 1 := by
  simp [dehomogenize]

@[simp]
theorem dehomogenize_X_of_ne [CommSemiring R] (i j : ι) (hj : j ≠ i) :
    dehomogenize (R := R) i (X j) = X ⟨j, hj⟩ := by
  simp [dehomogenize, hj]

/-- Evaluation commutes with the concrete dehomogenizing substitution. -/
theorem eval_dehomogenize [CommSemiring R] (i : ι) (f : MvPolynomial ι R)
    (x : {j : ι // j ≠ i} → R) :
    eval x (dehomogenize i f) = eval (insertOne i x) f := by
  classical
  change eval x (eval₂ C (insertOne i X) f) = _
  rw [← eval_assoc]
  apply congrArg (fun v : ι → R => eval v f)
  funext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [Function.comp_apply, hj]

variable [Field K]

/-- Filling in the missing chart coordinate recovers normalized homogeneous
coordinates of the same projective point. -/
theorem insertOne_affineChart (i : ι) (p : Projectivization K (ι → K))
    (hp : ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p) :
    insertOne i (ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.affineChart i ⟨p, hp⟩) = ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i p := by
  funext j
  by_cases hj : j = i
  · subst j
    rw [insertOne_self, ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates_self i p hp]
  · rw [insertOne_of_ne i j _ hj]
    rfl

/-- The affine polynomial obtained by dehomogenization evaluates on the chart
exactly as the original polynomial evaluates on normalized coordinates. -/
theorem eval_dehomogenize_affineChart (i : ι) (f : MvPolynomial ι K)
    (p : Projectivization K (ι → K)) (hp : ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p) :
    eval (ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.affineChart i ⟨p, hp⟩) (dehomogenize i f) = eval (ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i p) f := by
  rw [eval_dehomogenize, insertOne_affineChart]

/-- The normalization factor for a homogeneous polynomial of degree `d`. -/
theorem eval_coordinates_mk (i : ι) (f : MvPolynomial ι K) {d : ℕ}
    (hf : f.IsHomogeneous d) (v : ι → K) (hv : v ≠ 0) :
    eval (ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (Projectivization.mk K v hv)) f =
      (v i)⁻¹ ^ d * eval v f := by
  have hcoords : ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i (Projectivization.mk K v hv) = (v i)⁻¹ • v := by
    funext j
    simp [div_eq_mul_inv, mul_comm]
  rw [hcoords]
  exact HomogeneousEvalMap.eval_smul_of_isHomogeneous hf (v i)⁻¹ v

/-- Evaluation of an affine dehomogenization in terms of any homogeneous
representative whose selected coordinate is nonzero. -/
theorem eval_dehomogenize_affineChart_mk (i : ι) (f : MvPolynomial ι K) {d : ℕ}
    (hf : f.IsHomogeneous d) (v : ι → K) (hv : v ≠ 0) (hi : v i ≠ 0) :
    eval (ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.affineChart i ⟨Projectivization.mk K v hv, (ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff i v hv).mpr hi⟩)
      (dehomogenize i f) = (v i)⁻¹ ^ d * eval v f := by
  rw [eval_dehomogenize_affineChart]
  exact eval_coordinates_mk i f hf v hv

/-- A homogeneous projective equation on a standard patch is precisely its
ordinary dehomogenized affine polynomial equation. -/
theorem mem_projectiveZeroLocus_iff_dehomogenize (i : ι) (f : MvPolynomial ι K)
    {d : ℕ} (hf : f.IsHomogeneous d) (p : Projectivization K (ι → K))
    (hp : ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p) :
    p ∈ ProjectiveZeroLocus.homogeneousProjectiveZeroLocus f hf ↔
      eval (ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.affineChart i ⟨p, hp⟩) (dehomogenize i f) = 0 := by
  rw [eval_dehomogenize_affineChart]
  exact ProjectiveZeroLocus.mem_homogeneousProjectiveZeroLocus_iff f hf p (ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i p)
    (ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.normalized_ne_zero i _ hp) (ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.mk_coordinates i p hp)

/-- The same chart identification for any family of homogeneous equations. -/
theorem mem_projectiveCommonZeroLocus_iff_dehomogenize {κ : Type*} (i : ι)
    (f : κ → MvPolynomial ι K) (d : κ → ℕ) (hf : ∀ k, (f k).IsHomogeneous (d k))
    (p : Projectivization K (ι → K)) (hp : ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p) :
    p ∈ ProjectiveZeroLocus.projectiveCommonZeroLocus f d hf ↔
      ∀ k, eval (ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.affineChart i ⟨p, hp⟩) (dehomogenize i (f k)) = 0 := by
  simp only [ProjectiveZeroLocus.projectiveCommonZeroLocus, Set.mem_iInter]
  exact forall_congr' fun k => mem_projectiveZeroLocus_iff_dehomogenize i (f k) (hf k) p hp

end OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization
