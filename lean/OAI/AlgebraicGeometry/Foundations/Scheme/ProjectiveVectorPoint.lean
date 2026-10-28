import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace
import Mathlib.RingTheory.Ideal.Maps

/-! # Projective Vector Point -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveVectorPoint

noncomputable section

/-!
# Actual projective scheme points from homogeneous coordinates

A nonzero complex vector defines a scheme morphism from `Spec ℂ` to the
standard projective scheme, using mathlib's construction from global sections.
The morphism is proved to be over `Spec ℂ`, and its homogeneous basic-open
membership is identified with ordinary polynomial evaluation.
-/

set_option autoImplicit false
set_option warningAsError true

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {n : ℕ}

/-- Evaluate homogeneous coordinates, then view the resulting complex number
as a global section of the actual affine scheme `Spec ℂ`. -/
def vectorGlobalSections (v : Fin (n + 1) → ℂ) :
    ProjectiveSpace.homogeneousCoordinateRing n →+* Γ(ProjectiveSpace.complexBase, ⊤) :=
  (Scheme.ΓSpecIso (.of ℂ)).inv.hom.comp (MvPolynomial.eval v)

@[simp]
theorem vectorGlobalSections_apply (v : Fin (n + 1) → ℂ)
    (f : ProjectiveSpace.homogeneousCoordinateRing n) :
    vectorGlobalSections v f = (Scheme.ΓSpecIso (.of ℂ)).inv (MvPolynomial.eval v f) := rfl

@[simp]
theorem vectorGlobalSections_X (v : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    vectorGlobalSections v (MvPolynomial.X i) = (Scheme.ΓSpecIso (.of ℂ)).inv (v i) := by
  simp [vectorGlobalSections]

/-- A nonzero coordinate vector makes the image of the irrelevant ideal
contain a unit. This is the genuine hypothesis required by the `Proj` map. -/
theorem vectorGlobalSections_map_irrelevant_eq_top (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) :
    (HomogeneousIdeal.irrelevant (ProjectiveSpace.projectiveGrading n)).toIdeal.map
      (vectorGlobalSections v) = ⊤ := by
  classical
  have hn : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hn
  have hX : (MvPolynomial.X i : ProjectiveSpace.homogeneousCoordinateRing n) ∈
      (HomogeneousIdeal.irrelevant (ProjectiveSpace.projectiveGrading n)).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.zero_lt_one (MvPolynomial.isHomogeneous_X ℂ i)
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem (vectorGlobalSections v) hX)
  rw [vectorGlobalSections_X]
  exact (isUnit_iff_ne_zero.mpr hi).map (Scheme.ΓSpecIso (.of ℂ)).inv.hom

/-- The scheme-theoretic complex point with homogeneous coordinates v. -/
def projectiveVectorPoint (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) :
    ProjectiveSpace.complexBase ⟶ ProjectiveSpace.projectiveSpace n :=
  Proj.fromOfGlobalSections (ProjectiveSpace.projectiveGrading n) (vectorGlobalSections v)
    (vectorGlobalSections_map_irrelevant_eq_top v hv)

/-- Pulling back a homogeneous projective basic open amounts to testing
whether its polynomial evaluation is nonzero on `Spec ℂ`. -/
theorem projectiveVectorPoint_preimage_basicOpen (v : Fin (n + 1) → ℂ) (hv : v ≠ 0)
    (f : ProjectiveSpace.homogeneousCoordinateRing n) {d : ℕ} (hd : 0 < d)
    (hf : f ∈ ProjectiveSpace.projectiveGrading n d) :
    projectiveVectorPoint v hv ⁻¹ᵁ Proj.basicOpen (ProjectiveSpace.projectiveGrading n) f =
      PrimeSpectrum.basicOpen (MvPolynomial.eval v f) := by
  rw [projectiveVectorPoint, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ hd hf]
  exact basicOpen_eq_of_affine (R := .of ℂ) (MvPolynomial.eval v f)

/-- Membership of the underlying point in any positive-degree homogeneous
basic open is exactly nonvanishing of ordinary evaluation. -/
theorem projectiveVectorPoint_mem_basicOpen_iff (v : Fin (n + 1) → ℂ) (hv : v ≠ 0)
    (f : ProjectiveSpace.homogeneousCoordinateRing n) {d : ℕ} (hd : 0 < d)
    (hf : f ∈ ProjectiveSpace.projectiveGrading n d) (x : ProjectiveSpace.complexBase) :
    projectiveVectorPoint v hv x ∈ Proj.basicOpen (ProjectiveSpace.projectiveGrading n) f ↔
      MvPolynomial.eval v f ≠ 0 := by
  change x ∈ projectiveVectorPoint v hv ⁻¹ᵁ Proj.basicOpen (ProjectiveSpace.projectiveGrading n) f ↔ _
  rw [projectiveVectorPoint_preimage_basicOpen v hv f hd hf]
  change x ∈ PrimeSpectrum.basicOpen (MvPolynomial.eval v f) ↔ _
  rw [Subsingleton.elim x (default : ProjectiveSpace.complexBase)]
  change (MvPolynomial.eval v f ∉ (default : ProjectiveSpace.complexBase).asIdeal) ↔ _
  rw [Scheme.default_asIdeal]
  rfl

/-- In particular, the standard i-th projective chart contains this point
exactly when its i-th homogeneous coordinate is nonzero. -/
@[simp]
theorem projectiveVectorPoint_mem_coordinateOpen_iff (v : Fin (n + 1) → ℂ) (hv : v ≠ 0)
    (i : Fin (n + 1)) (x : ProjectiveSpace.complexBase) :
    projectiveVectorPoint v hv x ∈ Proj.basicOpen (ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i) ↔
      v i ≠ 0 := by
  simpa using projectiveVectorPoint_mem_basicOpen_iff v hv (MvPolynomial.X i)
    Nat.zero_lt_one (MvPolynomial.isHomogeneous_X ℂ i) x

/-- The constructed point is a morphism over the complex base, not merely an
unstructured scheme morphism into the projective scheme. -/
@[reassoc (attr := simp)]
theorem projectiveVectorPoint_over_base (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) :
    projectiveVectorPoint v hv ≫ ProjectiveSpace.projectiveSpaceToBase n = 𝟙 ProjectiveSpace.complexBase := by
  have hc : CommRingCat.ofHom (ProjectiveSpace.degreeZeroConstants n).toRingHom ≫
      CommRingCat.ofHom ((vectorGlobalSections v).comp
        (algebraMap (ProjectiveSpace.projectiveGrading n 0) (ProjectiveSpace.homogeneousCoordinateRing n))) =
      (Scheme.ΓSpecIso (.of ℂ)).inv := by
    ext c
    change (Scheme.ΓSpecIso (.of ℂ)).inv (MvPolynomial.eval v (MvPolynomial.C c)) =
      (Scheme.ΓSpecIso (.of ℂ)).inv c
    simp
  rw [ProjectiveSpace.projectiveSpaceToBase, ← Category.assoc, projectiveVectorPoint,
    Proj.fromOfGlobalSections_toSpecZero, Category.assoc, ← Spec.map_comp, hc]
  exact toSpecΓ_SpecMap_ΓSpecIso_inv (.of ℂ)

end

end OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveVectorPoint
