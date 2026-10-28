import OAI.AlgebraicGeometry.HilbertScheme.Presentations.InfiniteFieldBound
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.IntegerQuotient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CoverModule

/-! # Change Quotient -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.ChangeQuotient.GradedHilbert

noncomputable section

/-! A coordinate change identifies the actual homogeneous quotient modules, with the target action given by evaluation. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CoverModule.ProjectiveCech

universe u

variable {K : Type u} [Field K] {n : ℕ}
variable (e : Hilbert.Polynomial.GradedHilbert.grading K n 1 ≃ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n 1) (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n))

def linearChangeQuotientEquiv :
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ (InfiniteFieldBound.GradedHilbert.changedIdeal e I).toIdeal) ≃ₐ[K] Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal :=
  Ideal.quotientEquivAlg _ _ (Changes.GradedHilbert.extendLinearEquiv e)
    (Ideal.map_comap_of_surjective (Changes.GradedHilbert.extendLinearEquiv e).toRingHom (Changes.GradedHilbert.extendLinearEquiv e).surjective I.toIdeal).symm

theorem linearChangeQuotientEquiv_mk (p : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) :
    linearChangeQuotientEquiv e I (Ideal.Quotient.mk (InfiniteFieldBound.GradedHilbert.changedIdeal e I).toIdeal p) =
      Ideal.Quotient.mk I.toIdeal (Changes.GradedHilbert.extendLinearEquiv e p) := rfl

theorem extendLinearEquiv_integer_homogeneous {d : ℤ} {p : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n}
    (hp : p ∈ WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := Fin (n + 1)) K d) :
    Changes.GradedHilbert.extendLinearEquiv e p ∈ WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := Fin (n + 1)) K d :=
  PolynomialSubstitution.GradedModules.linearSubstitution_integer_homogeneous K (fun i => (e (Changes.GradedHilbert.linearVariable i)).val)
    (fun i => (e (Changes.GradedHilbert.linearVariable i)).property) hp

theorem linearChangeQuotientEquiv_homogeneous (d : ℤ)
    (x : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ (InfiniteFieldBound.GradedHilbert.changedIdeal e I).toIdeal)
    (hx : x ∈ Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading (InfiniteFieldBound.GradedHilbert.changedIdeal e I) d) :
    linearChangeQuotientEquiv e I x ∈ Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I d := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨Changes.GradedHilbert.extendLinearEquiv e p, extendLinearEquiv_integer_homogeneous e hp, rfl⟩

@[instance_reducible]
def linearChangeQuotientModule : Module (MvPolynomial (Fin (n + 1)) K) (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal) :=
  Polynomial.CoverModule.ProjectiveCech.polynomialCoverModule K (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal)
    (fun i => (e (Changes.GradedHilbert.linearVariable i)).val)

theorem linearChangeQuotient_scalarTower :
    let := linearChangeQuotientModule e I
    let : SMul (MvPolynomial (Fin (n + 1)) K) (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal) :=
      (linearChangeQuotientModule e I).toSMul
    IsScalarTower K (MvPolynomial (Fin (n + 1)) K) (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal) := by
  let := linearChangeQuotientModule e I
  let : SMul (MvPolynomial (Fin (n + 1)) K) (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal) :=
    (linearChangeQuotientModule e I).toSMul
  apply @IsScalarTower.of_algebraMap_smul K (MvPolynomial (Fin (n + 1)) K)
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal) _ _ _ (linearChangeQuotientModule e I).toMulAction _
  intro r x
  change Ideal.Quotient.mk I.toIdeal
    (MvPolynomial.aeval (fun i => (e (Changes.GradedHilbert.linearVariable i)).val) (C r)) * x = r • x
  rw [MvPolynomial.aeval_C]
  exact (Algebra.smul_def r x).symm

theorem linearChangeQuotient_gradedSMul :
    let := linearChangeQuotientModule e I
    let : SMul (MvPolynomial (Fin (n + 1)) K) (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal) :=
      (linearChangeQuotientModule e I).toSMul
    SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := Fin (n + 1)) K) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) := by
  let := linearChangeQuotientModule e I
  let : SMul (MvPolynomial (Fin (n + 1)) K) (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal) :=
    (linearChangeQuotientModule e I).toSMul
  constructor
  intro d t p x hp hx
  obtain ⟨b, hb, rfl⟩ := hx
  refine ⟨Changes.GradedHilbert.extendLinearEquiv e p * b,
    SetLike.mul_mem_graded (extendLinearEquiv_integer_homogeneous e hp) hb, ?_⟩
  change Ideal.Quotient.mk I.toIdeal (Changes.GradedHilbert.extendLinearEquiv e p * b) =
    Ideal.Quotient.mk I.toIdeal (Changes.GradedHilbert.extendLinearEquiv e p) * Ideal.Quotient.mk I.toIdeal b
  exact map_mul _ _ _

def linearChangeQuotientPolynomialEquiv :
    let := Polynomial.CoverModule.ProjectiveCech.polynomialCoverModule K (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal)
      (fun i => (e (Changes.GradedHilbert.linearVariable i)).val)
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ (InfiniteFieldBound.GradedHilbert.changedIdeal e I).toIdeal) ≃ₗ[Hilbert.Polynomial.GradedHilbert.CoordinateRing K n]
      Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal := by
  let := Polynomial.CoverModule.ProjectiveCech.polynomialCoverModule K (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal)
    (fun i => (e (Changes.GradedHilbert.linearVariable i)).val)
  refine { (linearChangeQuotientEquiv e I).toAddEquiv with map_smul' := ?_ }
  intro a x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change linearChangeQuotientEquiv e I (Ideal.Quotient.mk _ (a * p)) =
    Ideal.Quotient.mk _ ((Changes.GradedHilbert.extendLinearEquiv e a) * (Changes.GradedHilbert.extendLinearEquiv e p))
  rw [linearChangeQuotientEquiv_mk, map_mul]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.ChangeQuotient.GradedHilbert
