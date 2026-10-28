import OAI.AlgebraicGeometry.ComplexPoints.Analytic.Affine
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.Nullstellensatz

/-! # Polynomial Zero Locus -/

namespace OAI.AlgebraicGeometry

/-!
# Euclidean closedness of complex polynomial zero loci

The topology on `ι → ℂ` is its usual product topology. In particular, when `ι` is
finite this is the ordinary Euclidean topology on complex affine space, not the
Zariski topology. The ideal zero locus below is mathlib's `MvPolynomial.zeroLocus`.
-/

variable {ι : Type*}

/-- Every level set of a complex multivariable polynomial is Euclidean closed. -/
theorem ComplexPoints.Analytic.PolynomialZeroLocus.isClosed_mvPolynomial_levelSet (p : MvPolynomial ι ℂ) (z : ℂ) :
    IsClosed {x : ι → ℂ | MvPolynomial.eval x p = z} :=
  isClosed_eq p.continuous_eval continuous_const

/-- The zero set of a complex multivariable polynomial is Euclidean closed. -/
theorem ComplexPoints.Analytic.PolynomialZeroLocus.isClosed_mvPolynomial_zeroSet (p : MvPolynomial ι ℂ) :
    IsClosed {x : ι → ℂ | MvPolynomial.eval x p = 0} :=
  ComplexPoints.Analytic.PolynomialZeroLocus.isClosed_mvPolynomial_levelSet p 0

/-- Arbitrary simultaneous polynomial equations define a Euclidean closed set. -/
theorem ComplexPoints.Analytic.PolynomialZeroLocus.isClosed_mvPolynomial_commonZeroSet (S : Set (MvPolynomial ι ℂ)) :
    IsClosed {x : ι → ℂ | ∀ p ∈ S, MvPolynomial.eval x p = 0} := by
  have hset : {x : ι → ℂ | ∀ p ∈ S, MvPolynomial.eval x p = 0} =
      ⋂ p ∈ S, {x : ι → ℂ | MvPolynomial.eval x p = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hset]
  exact isClosed_biInter fun p _ => ComplexPoints.Analytic.PolynomialZeroLocus.isClosed_mvPolynomial_zeroSet p

/-- Mathlib's affine algebraic zero locus is also closed for the Euclidean topology. -/
theorem ComplexPoints.Analytic.PolynomialZeroLocus.isClosed_mvPolynomial_zeroLocus (I : Ideal (MvPolynomial ι ℂ)) :
    IsClosed (MvPolynomial.zeroLocus ℂ I) := by
  simpa only [MvPolynomial.zeroLocus, MvPolynomial.aeval_eq_eval, SetLike.mem_coe] using
    ComplexPoints.Analytic.PolynomialZeroLocus.isClosed_mvPolynomial_commonZeroSet (I : Set (MvPolynomial ι ℂ))

/-- Replacing equations by their generated ideal gives the same Euclidean zero set. -/
theorem ComplexPoints.Analytic.PolynomialZeroLocus.mvPolynomial_zeroLocus_span_eq (S : Set (MvPolynomial ι ℂ)) :
    MvPolynomial.zeroLocus ℂ (Ideal.span S) =
      {x : ι → ℂ | ∀ p ∈ S, MvPolynomial.eval x p = 0} := by
  simpa only [MvPolynomial.aeval_eq_eval] using MvPolynomial.zeroLocus_span (K := ℂ) S

/-- A polynomial's nonvanishing locus is open in ordinary complex affine space. -/
theorem ComplexPoints.Analytic.PolynomialZeroLocus.isOpen_mvPolynomial_nonzeroSet (p : MvPolynomial ι ℂ) :
    IsOpen {x : ι → ℂ | MvPolynomial.eval x p ≠ 0} :=
  (ComplexPoints.Analytic.PolynomialZeroLocus.isClosed_mvPolynomial_zeroSet p).isOpen_compl

/-- Continuous coordinate maps pull polynomial equations back to closed sets. -/
theorem ComplexPoints.Analytic.PolynomialZeroLocus.isClosed_mvPolynomial_commonZeroSet_preimage {X : Type*} [TopologicalSpace X]
    (f : X → ι → ℂ) (hf : Continuous f) (S : Set (MvPolynomial ι ℂ)) :
    IsClosed {x : X | ∀ p ∈ S, MvPolynomial.eval (f x) p = 0} :=
  (ComplexPoints.Analytic.PolynomialZeroLocus.isClosed_mvPolynomial_commonZeroSet S).preimage hf

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- The zero set of a regular function on affine complex points is closed. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosed_zeroSet (a : A) :
    IsClosed {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A | x a = 0} :=
  isClosed_eq (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval a) continuous_const

/-- Arbitrary regular-function equations define a closed set of affine complex points. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosed_commonZeroSet (S : Set A) :
    IsClosed {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A | ∀ a ∈ S, x a = 0} := by
  have hset : {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A | ∀ a ∈ S, x a = 0} =
      ⋂ a ∈ S, {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A | x a = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hset]
  exact isClosed_biInter fun a _ => Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosed_zeroSet a

/-- The points whose characters kill a fixed ideal form a closed set. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosed_zeroLocus (I : Ideal A) :
    IsClosed {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A | I ≤ RingHom.ker x.toRingHom} := by
  have hset : {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A | I ≤ RingHom.ker x.toRingHom} =
      {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A | ∀ a ∈ (I : Set A), x a = 0} := by
    ext x
    constructor
    · intro hx a ha
      exact hx ha
    · intro hx a ha
      exact hx a ha
  rw [hset]
  exact Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosed_commonZeroSet (I : Set A)

/-- Principal nonvanishing loci are open for the ordinary affine-point topology. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpen_nonzeroSet (a : A) :
    IsOpen {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A | x a ≠ 0} :=
  (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosed_zeroSet a).isOpen_compl

end OAI.AlgebraicGeometry
