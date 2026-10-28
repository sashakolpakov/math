import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-! # Standard Smooth Dimension -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.StandardSmoothDimension.Algebraic

/-!
# Intrinsic dimension of standard smooth presentations

Finite submersive presentations of a nontrivial algebra have equal dimension:
that dimension is the rank of its actual module of Kähler differentials. The
same dimension persists under principal localization and under nontrivial base
change. These comparisons provide algebraic dimension compatibility for charts.
-/

open scoped TensorProduct

universe u v w t

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The relative dimension of a nontrivial standard smooth algebra is unique. -/
theorem standardSmooth_dimension_unique [Nontrivial S] (n m : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    [Algebra.IsStandardSmoothOfRelativeDimension m R S] : n = m := by
  apply Nat.cast_injective (R := Cardinal)
  exact (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := R) (S := S) n).symm.trans
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
      (R := R) (S := S) m)

/-- Any finite submersive presentation computes the intrinsic relative dimension. -/
theorem standardSmooth_dimension_eq_presentation [Nontrivial S] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    {ι : Type w} {σ : Type t} [Finite ι] [Finite σ]
    (P : Algebra.SubmersivePresentation R S ι σ) : n = P.dimension := by
  apply Nat.cast_injective (R := Cardinal)
  exact (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := R) (S := S) n).symm.trans P.rank_kaehlerDifferential

/-- Two finite submersive presentations of the same nontrivial algebra have equal dimension. -/
theorem submersivePresentation_dimension_eq [Nontrivial S]
    {ι : Type w} {σ : Type t} {κ τ : Type*}
    [Finite ι] [Finite σ] [Finite κ] [Finite τ]
    (P : Algebra.SubmersivePresentation R S ι σ)
    (Q : Algebra.SubmersivePresentation R S κ τ) : P.dimension = Q.dimension := by
  apply Nat.cast_injective (R := Cardinal)
  exact P.rank_kaehlerDifferential.symm.trans Q.rank_kaehlerDifferential

/-- Principal localization preserves a proved standard-smooth relative dimension. -/
theorem standardSmoothDimension_localizationAway
    {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (n : ℕ) (r : S) [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    [IsLocalization.Away r T] : Algebra.IsStandardSmoothOfRelativeDimension n R T := by
  let : Algebra.IsStandardSmoothOfRelativeDimension 0 S T :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away r
  simpa only [Nat.zero_add] using
    (Algebra.IsStandardSmoothOfRelativeDimension.trans R S T (n := n) (m := 0))

/-- A presentation of a nonempty principal localization has the original presentation dimension. -/
theorem submersivePresentation_dimension_localizationAway
    {T : Type*} [CommRing T] [Nontrivial T]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (r : S) [IsLocalization.Away r T]
    {ι : Type w} {σ : Type t} {κ τ : Type*}
    [Finite ι] [Finite σ] [Finite κ] [Finite τ]
    (P : Algebra.SubmersivePresentation R S ι σ)
    (Q : Algebra.SubmersivePresentation R T κ τ) : P.dimension = Q.dimension := by
  let : Algebra.IsStandardSmoothOfRelativeDimension P.dimension R S :=
    P.isStandardSmoothOfRelativeDimension rfl
  let : Algebra.IsStandardSmoothOfRelativeDimension P.dimension R T :=
    standardSmoothDimension_localizationAway (R := R) P.dimension r
  exact standardSmooth_dimension_eq_presentation P.dimension Q

/-- A presentation after nontrivial scalar base change has the original relative dimension. -/
theorem submersivePresentation_dimension_baseChange
    {T : Type*} [CommRing T] [Algebra R T] [Nontrivial (T ⊗[R] S)]
    {ι : Type w} {σ : Type t} {κ τ : Type*}
    [Finite ι] [Finite σ] [Finite κ] [Finite τ]
    (P : Algebra.SubmersivePresentation R S ι σ)
    (Q : Algebra.SubmersivePresentation T (T ⊗[R] S) κ τ) :
    P.dimension = Q.dimension := by
  let : Algebra.IsStandardSmoothOfRelativeDimension P.dimension R S :=
    P.isStandardSmoothOfRelativeDimension rfl
  exact standardSmooth_dimension_eq_presentation P.dimension Q

end OAI.AlgebraicGeometry.Foundations.Scheme.StandardSmoothDimension.Algebraic
