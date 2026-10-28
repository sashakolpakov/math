import OAI.AlgebraicGeometry.Foundations.Scheme.HomogeneousEvalMap
import Mathlib.LinearAlgebra.Projectivization.Basic

/-! # Projective Zero Locus -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveZeroLocus

/-!
# Homogeneous polynomial zero loci on projective space

A homogeneous polynomial need not define a scalar-valued function on projective space,
but its vanishing does descend. This file constructs that descended set using the
actual quotient `Projectivization` and proves its representative criterion.

This is a set-level construction. No identification with the analytic complex points
of a projective scheme, or with the scheme's closed subschemes, is asserted here.
-/

open _root_.MvPolynomial

variable {K : Type*} {ι : Type*} [Field K]

/-- The projective vanishing locus of a homogeneous polynomial. -/
def homogeneousProjectiveZeroLocus (f : MvPolynomial ι K) {d : ℕ}
    (hf : f.IsHomogeneous d) : Set (Projectivization K (ι → K)) :=
  fun p => Projectivization.lift
    (fun (v : {v : ι → K // v ≠ 0}) => eval (v : ι → K) f = 0)
    (by
      intro a b c h
      apply propext
      have hc : c ≠ 0 := by
        intro hc
        apply a.property
        simpa only [hc, zero_smul] using h
      rw [h]
      exact HomogeneousEvalMap.eval_smul_eq_zero_iff hf hc (b : ι → K)) p

@[simp]
theorem mem_homogeneousProjectiveZeroLocus_mk (f : MvPolynomial ι K) {d : ℕ}
    (hf : f.IsHomogeneous d) (v : ι → K) (hv : v ≠ 0) :
    Projectivization.mk K v hv ∈ homogeneousProjectiveZeroLocus f hf ↔
      eval v f = 0 :=
  Iff.rfl

/-- The vanishing test may be made on any nonzero representative. -/
theorem mem_homogeneousProjectiveZeroLocus_iff (f : MvPolynomial ι K) {d : ℕ}
    (hf : f.IsHomogeneous d) (p : Projectivization K (ι → K))
    (v : ι → K) (hv : v ≠ 0) (hp : Projectivization.mk K v hv = p) :
    p ∈ homogeneousProjectiveZeroLocus f hf ↔ eval v f = 0 := by
  subst p
  exact mem_homogeneousProjectiveZeroLocus_mk f hf v hv

/-- The chosen representative in mathlib gives the same test. -/
theorem mem_homogeneousProjectiveZeroLocus_rep (f : MvPolynomial ι K) {d : ℕ}
    (hf : f.IsHomogeneous d) (p : Projectivization K (ι → K)) :
    p ∈ homogeneousProjectiveZeroLocus f hf ↔ eval p.rep f = 0 :=
  mem_homogeneousProjectiveZeroLocus_iff f hf p p.rep p.rep_nonzero p.mk_rep

/-- Equivalently, a homogeneous polynomial vanishes on some representative. -/
theorem mem_homogeneousProjectiveZeroLocus_exists (f : MvPolynomial ι K) {d : ℕ}
    (hf : f.IsHomogeneous d) (p : Projectivization K (ι → K)) :
    p ∈ homogeneousProjectiveZeroLocus f hf ↔
      ∃ (v : ι → K) (hv : v ≠ 0), Projectivization.mk K v hv = p ∧ eval v f = 0 := by
  constructor
  · intro hp
    exact ⟨p.rep, p.rep_nonzero, p.mk_rep,
      (mem_homogeneousProjectiveZeroLocus_rep f hf p).mp hp⟩
  · rintro ⟨v, hv, hp, hzero⟩
    exact (mem_homogeneousProjectiveZeroLocus_iff f hf p v hv hp).mpr hzero

/-- Equivalently, it vanishes on every representative. -/
theorem mem_homogeneousProjectiveZeroLocus_forall (f : MvPolynomial ι K) {d : ℕ}
    (hf : f.IsHomogeneous d) (p : Projectivization K (ι → K)) :
    p ∈ homogeneousProjectiveZeroLocus f hf ↔
      ∀ (v : ι → K) (hv : v ≠ 0), Projectivization.mk K v hv = p → eval v f = 0 := by
  constructor
  · intro hp v hv hrep
    exact (mem_homogeneousProjectiveZeroLocus_iff f hf p v hv hrep).mp hp
  · intro hp
    exact (mem_homogeneousProjectiveZeroLocus_rep f hf p).mpr
      (hp p.rep p.rep_nonzero p.mk_rep)

/-- Changing the proof or the degree of homogeneity does not change the vanishing set. -/
theorem homogeneousProjectiveZeroLocus_eq (f : MvPolynomial ι K) {d e : ℕ}
    (hf : f.IsHomogeneous d) (hg : f.IsHomogeneous e) :
    homogeneousProjectiveZeroLocus f hf = homogeneousProjectiveZeroLocus f hg := by
  ext p
  rw [mem_homogeneousProjectiveZeroLocus_rep, mem_homogeneousProjectiveZeroLocus_rep]

/-- A family of homogeneous equations cuts out their intersection. -/
def projectiveCommonZeroLocus {κ : Type*} (f : κ → MvPolynomial ι K)
    (d : κ → ℕ) (hf : ∀ k, (f k).IsHomogeneous (d k)) :
    Set (Projectivization K (ι → K)) :=
  ⋂ k, homogeneousProjectiveZeroLocus (f k) (hf k)

@[simp]
theorem mem_projectiveCommonZeroLocus_mk {κ : Type*} (f : κ → MvPolynomial ι K)
    (d : κ → ℕ) (hf : ∀ k, (f k).IsHomogeneous (d k)) (v : ι → K) (hv : v ≠ 0) :
    Projectivization.mk K v hv ∈ projectiveCommonZeroLocus f d hf ↔
      ∀ k, eval v (f k) = 0 := by
  simp [projectiveCommonZeroLocus]

/-- A degree-zero equation is constant, so it either cuts out everything or nothing. -/
@[simp]
theorem mem_homogeneousProjectiveZeroLocus_C (c : K)
    (p : Projectivization K (ι → K)) :
    p ∈ homogeneousProjectiveZeroLocus (C c) (isHomogeneous_C ι c) ↔ c = 0 := by
  rw [mem_homogeneousProjectiveZeroLocus_rep]
  simp

@[simp]
theorem homogeneousProjectiveZeroLocus_zero (d : ℕ) :
    homogeneousProjectiveZeroLocus (0 : MvPolynomial ι K)
      (isHomogeneous_zero ι K d) = Set.univ := by
  ext p
  rw [mem_homogeneousProjectiveZeroLocus_rep]
  simp

/-- A nonzero constant has empty projective zero locus, also in degree zero. -/
theorem homogeneousProjectiveZeroLocus_C_of_ne_zero (c : K) (hc : c ≠ 0) :
    homogeneousProjectiveZeroLocus (C c : MvPolynomial ι K)
      (isHomogeneous_C ι c) = ∅ := by
  ext p
  simp [hc]

/-- Product equations give the union of their projective vanishing loci. -/
theorem homogeneousProjectiveZeroLocus_mul (f g : MvPolynomial ι K) {d e : ℕ}
    (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous e) :
    homogeneousProjectiveZeroLocus (f * g) (hf.mul hg) =
      homogeneousProjectiveZeroLocus f hf ∪ homogeneousProjectiveZeroLocus g hg := by
  ext p
  simp only [Set.mem_union, mem_homogeneousProjectiveZeroLocus_rep, map_mul, mul_eq_zero]

end OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveZeroLocus
