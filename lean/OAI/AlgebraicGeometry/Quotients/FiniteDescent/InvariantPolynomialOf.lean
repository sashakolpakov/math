import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantBasisOf
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Algebra.Polynomial.Lifts

/-! # Invariant Polynomial Of -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantPolynomialOf.Construction.InvariantPolynomial

/-!
# Invariant characteristic polynomials

We prove the finite-free ring calculations used to construct affine quotients.
Compatible source and target base changes make the characteristic polynomial
of a target-valued element invariant. Cayley-Hamilton then proves integrality
over the actual invariant subring.
-/

open _root_.Module
open scoped BigOperators

universe u v w z

section BaseChange

variable {R S A B ι : Type*}
variable [CommRing R] [CommRing S] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra S B] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Coordinates commute with a ring base change carrying a basis to a basis. -/
theorem repr_map_of_basis
    (φ : R →+* S) (f : A →+* B)
    (hf : ∀ r, f (algebraMap R A r) = algebraMap S B (φ r))
    (b : Basis ι R A) (d : Basis ι S B) (hd : ∀ i, d i = f (b i))
    (a : A) (i : ι) :
    d.repr (f a) i = φ (b.repr a i) := by
  classical
  have hsum : ∑ j, φ (b.repr a j) • d j = f a := by
    calc
      _ = f (∑ j, b.repr a j • b j) := by
        simp only [map_sum, Algebra.smul_def, map_mul, hf, hd]
      _ = f a := congrArg f (b.sum_repr a)
  exact (d.linearIndependent.eq_coords_of_eq
    (hsum.trans (d.sum_repr (f a)).symm) i).symm

/-- Matrices for multiplication commute with the same basis base change. -/
theorem leftMulMatrix_map_of_basis
    (φ : R →+* S) (f : A →+* B)
    (hf : ∀ r, f (algebraMap R A r) = algebraMap S B (φ r))
    (b : Basis ι R A) (d : Basis ι S B) (hd : ∀ i, d i = f (b i))
    (a : A) :
    Algebra.leftMulMatrix d (f a) = (Algebra.leftMulMatrix b a).map φ := by
  ext i j
  simp only [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, hd, ← map_mul]
  exact repr_map_of_basis φ f hf b d hd (a * b j) i

/-- Norms commute with a ring base change carrying a basis to a basis. -/
theorem norm_map_of_basis
    (φ : R →+* S) (f : A →+* B)
    (hf : ∀ r, f (algebraMap R A r) = algebraMap S B (φ r))
    (b : Basis ι R A) (d : Basis ι S B) (hd : ∀ i, d i = f (b i))
    (a : A) :
    Algebra.norm S (f a) = φ (Algebra.norm R a) := by
  rw [Algebra.norm_eq_matrix_det d, Algebra.norm_eq_matrix_det b,
    leftMulMatrix_map_of_basis φ f hf b d hd]
  exact (RingHom.map_det φ _).symm

/-- Characteristic polynomials commute with the same ring base change. -/
theorem charpoly_map_of_basis
    (φ : R →+* S) (f : A →+* B)
    (hf : ∀ r, f (algebraMap R A r) = algebraMap S B (φ r))
    (b : Basis ι R A) (d : Basis ι S B) (hd : ∀ i, d i = f (b i))
    (a : A) :
    (Algebra.leftMulMatrix d (f a)).charpoly =
      (Algebra.leftMulMatrix b a).charpoly.map φ := by
  rw [leftMulMatrix_map_of_basis φ f hf b d hd, Matrix.charpoly_map]

/-- Determinants of families of vectors commute with a compatible basis base change. -/
theorem det_map_of_basis
    (φ : R →+* S) (f : A →+* B)
    (hf : ∀ r, f (algebraMap R A r) = algebraMap S B (φ r))
    (b : Basis ι R A) (d : Basis ι S B) (hd : ∀ i, d i = f (b i))
    (x : ι → A) :
    d.det (fun i => f (x i)) = φ (b.det x) := by
  rw [Basis.det_apply, Basis.det_apply]
  have hmatrix : d.toMatrix (fun i => f (x i)) = (b.toMatrix x).map φ := by
    ext i j
    exact repr_map_of_basis φ f hf b d hd (x j) i
  rw [hmatrix]
  exact (RingHom.map_det φ _).symm

/-- If one basis survives a compatible ring base change, every basis does. -/
theorem exists_basis_map
    (φ : R →+* S) (f : A →+* B)
    (hf : ∀ r, f (algebraMap R A r) = algebraMap S B (φ r))
    (b : Basis ι R A) (d : Basis ι S B) (hd : ∀ i, d i = f (b i))
    (e : Basis ι R A) :
    ∃ e' : Basis ι S B, ∀ i, e' i = f (e i) := by
  have hu : IsUnit (d.det (fun i => f (e i))) := by
    rw [det_map_of_basis φ f hf b d hd e]
    exact (b.isUnit_det e).map φ
  obtain ⟨hli, hspan⟩ := d.is_basis_iff_det.mpr hu
  exact ⟨Basis.mk hli hspan.ge, fun i => Basis.mk_apply hli hspan.ge i⟩

end BaseChange

variable {A : Type u} {B : Type v} {D : Type w} {ι : Type z}
variable [CommRing A] [CommRing B] [CommRing D]
variable [Algebra A B] [Algebra B D] [Fintype ι] [DecidableEq ι]

/-- The source and target ring maps agree on the norm of a target-valued element. -/
theorem norm_invariant
    (t : A →+* B) (p c : B →+* D)
    (hp : ∀ a, p (algebraMap A B a) = algebraMap B D (t a))
    (hc : ∀ a, c (algebraMap A B a) = algebraMap B D (algebraMap A B a))
    (hct : ∀ a, c (t a) = p (t a))
    (b : Basis ι A B) (dp dc : Basis ι B D)
    (hdp : ∀ i, dp i = p (b i)) (hdc : ∀ i, dc i = c (b i))
    (a : A) :
    algebraMap A B (Algebra.norm A (t a)) = t (Algebra.norm A (t a)) := by
  rw [← norm_map_of_basis (algebraMap A B) c hc b dc hdc,
    ← norm_map_of_basis t p hp b dp hdp, hct]

/-- The source and target ring maps agree on the characteristic polynomial
of multiplication by a target-valued element. -/
theorem charpoly_invariant
    (t : A →+* B) (p c : B →+* D)
    (hp : ∀ a, p (algebraMap A B a) = algebraMap B D (t a))
    (hc : ∀ a, c (algebraMap A B a) = algebraMap B D (algebraMap A B a))
    (hct : ∀ a, c (t a) = p (t a))
    (b : Basis ι A B) (dp dc : Basis ι B D)
    (hdp : ∀ i, dp i = p (b i)) (hdc : ∀ i, dc i = c (b i))
    (a : A) :
    (Algebra.leftMulMatrix b (t a)).charpoly.map (algebraMap A B) =
      (Algebra.leftMulMatrix b (t a)).charpoly.map t := by
  let : Module.Free B D := Module.Free.of_basis dp
  let : Module.Finite B D := Module.Finite.of_basis dp
  rw [← charpoly_map_of_basis (algebraMap A B) c hc b dc hdc,
    ← charpoly_map_of_basis t p hp b dp hdp]
  simp only [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, hct]

/-- Integrality over invariants is a consequence of the two base-change
bases and the groupoid composition identities. -/
theorem integral_over_invariants
    (t : A →+* B) (ht : Function.Injective t) (p c : B →+* D)
    (hp : ∀ a, p (algebraMap A B a) = algebraMap B D (t a))
    (hc : ∀ a, c (algebraMap A B a) = algebraMap B D (algebraMap A B a))
    (hct : ∀ a, c (t a) = p (t a))
    (b : Basis ι A B) (dp dc : Basis ι B D)
    (hdp : ∀ i, dp i = p (b i)) (hdc : ∀ i, dc i = c (b i))
    (a : A) :
    let C := (algebraMap A B).eqLocus t
    letI : Algebra C A := C.subtype.toAlgebra
    IsIntegral C a := by
  classical
  let C := (algebraMap A B).eqLocus t
  let : Algebra C A := C.subtype.toAlgebra
  let : Module.Free A B := Module.Free.of_basis b
  let : Module.Finite A B := Module.Finite.of_basis b
  let P := (Algebra.leftMulMatrix b (t a)).charpoly
  have hP : P.map (algebraMap A B) = P.map t :=
    charpoly_invariant t p c hp hc hct b dp dc hdp hdc a
  have hlift : P ∈ Polynomial.lifts C.subtype := by
    apply (Polynomial.lifts_iff_coeff_lifts P).mpr
    intro n
    refine ⟨⟨P.coeff n, ?_⟩, rfl⟩
    change algebraMap A B (P.coeff n) = t (P.coeff n)
    simpa only [Polynomial.coeff_map] using congrArg (fun q : Polynomial B => q.coeff n) hP
  obtain ⟨Q, hQ⟩ := (Polynomial.mem_lifts P).mp hlift
  have hmonic : Q.Monic := Polynomial.monic_of_injective
    (f := C.subtype) Subtype.val_injective (hQ.symm ▸ Matrix.charpoly_monic _)
  have hzero : P.eval₂ (algebraMap A B) (t a) = 0 := by
    change Polynomial.aeval (t a) P = 0
    simpa only [P, Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix] using
      Algebra.aeval_self_charpoly_lmul (R := A) (t a)
  have hroot : P.eval a = 0 := by
    apply ht
    rw [map_zero, ← Polynomial.eval_map_apply, ← hP, Polynomial.eval_map, hzero]
  refine ⟨Q, hmonic, ?_⟩
  change Q.eval₂ C.subtype a = 0
  rw [← Polynomial.eval_map, hQ, hroot]

/-- The determinant of a target-valued family changes by a unit under the
two structural maps. -/
theorem target_determinant_relation
    (t : A →+* B) (p c : B →+* D)
    (hp : ∀ a, p (algebraMap A B a) = algebraMap B D (t a))
    (hc : ∀ a, c (algebraMap A B a) = algebraMap B D (algebraMap A B a))
    (hct : ∀ a, c (t a) = p (t a))
    (b : Basis ι A B) (dp dc : Basis ι B D)
    (hdp : ∀ i, dp i = p (b i)) (hdc : ∀ i, dc i = c (b i))
    (x : ι → A) :
    t (b.det (fun i => t (x i))) =
      dp.det dc * algebraMap A B (b.det (fun i => t (x i))) := by
  rw [← det_map_of_basis t p hp b dp hdp,
    ← det_map_of_basis (algebraMap A B) c hc b dc hdc]
  simp only [hct, Basis.det_apply]
  rw [← Matrix.det_mul, Basis.toMatrix_mul_toMatrix]

/-- A determinant admits an invariant denominator with exactly the same
invertibility locus: the denominator is a unit times a power of the determinant. -/
theorem exists_invariant_denominator
    (t : A →+* B) (p c : B →+* D)
    (hp : ∀ a, p (algebraMap A B a) = algebraMap B D (t a))
    (hc : ∀ a, c (algebraMap A B a) = algebraMap B D (algebraMap A B a))
    (hct : ∀ a, c (t a) = p (t a))
    (b : Basis ι A B) (dp dc : Basis ι B D)
    (hdp : ∀ i, dp i = p (b i)) (hdc : ∀ i, dc i = c (b i))
    (x : ι → A) :
    ∃ g : (algebraMap A B).eqLocus t, ∃ v : Aˣ,
      (g : A) = (v : A) * (b.det (fun i => t (x i))) ^ Fintype.card ι := by
  let d := b.det (fun i => t (x i))
  let v := (dp.isUnit_det dc).unit
  refine ⟨⟨Algebra.norm A (t d), norm_invariant t p c hp hc hct b dp dc hdp hdc d⟩,
    Units.map (Algebra.norm A) v, ?_⟩
  change Algebra.norm A (t d) = Algebra.norm A (v : B) * d ^ Fintype.card ι
  have hv : (v : B) = dp.det dc := (dp.isUnit_det dc).unit_spec
  rw [hv, target_determinant_relation t p c hp hc hct b dp dc hdp hdc x,
    map_mul, Algebra.norm_algebraMap_of_basis b]

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantPolynomialOf.Construction.InvariantPolynomial
