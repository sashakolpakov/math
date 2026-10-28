import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Differential Rank Localization -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.DifferentialRankLocalization.Algebraic

noncomputable section

/-!
# Presentation dimensions measured in a common localization

The dimension of a submersive presentation can be computed after a nonzero
formally étale extension. In particular, affine charts of an integral scheme
can be compared in their common function field without presupposing their
dimensions are equal.
-/

open scoped TensorProduct

universe u v w t z

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable [Nontrivial S] [Nontrivial T]
variable {ι : Type t} {σ : Type z} [Finite ι] [Finite σ]

/-- The dimension of a submersive presentation is the rank of the differential
module after a nonzero formally étale extension. -/
theorem submersive_dimension_eq_differential_finrank
    [Algebra.FormallyEtale S T] (P : Algebra.SubmersivePresentation R S ι σ) :
    P.dimension = Module.finrank T Ω[T⁄R] := by
  let : Module.Free S Ω[S⁄R] := P.free_kaehlerDifferential
  have hdim : Module.finrank S Ω[S⁄R] = P.dimension :=
    Module.finrank_eq_of_rank_eq P.rank_kaehlerDifferential
  calc
    P.dimension = Module.finrank S Ω[S⁄R] := hdim.symm
    _ = Module.finrank T (T ⊗[S] Ω[S⁄R]) := Module.finrank_baseChange.symm
    _ = Module.finrank T Ω[T⁄R] :=
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).finrank_eq

/-- The preceding computation for any nonzero localization, including the
function field of a domain. -/
theorem submersive_dimension_eq_localized_differential_finrank
    (W : Submonoid S) [IsLocalization W T]
    (P : Algebra.SubmersivePresentation R S ι σ) :
    P.dimension = Module.finrank T Ω[T⁄R] := by
  let : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_isLocalization W
  exact submersive_dimension_eq_differential_finrank P

/-- Specialization to a common fraction field. -/
theorem submersive_dimension_eq_fraction_differential_finrank
    [IsFractionRing S T]
    (P : Algebra.SubmersivePresentation R S ι σ) :
    P.dimension = Module.finrank T Ω[T⁄R] :=
  submersive_dimension_eq_localized_differential_finrank (nonZeroDivisors S) P

/-- Standard smoothness itself therefore has the relative dimension measured
in any common fraction ring, independently of the chosen presentation. -/
theorem standardSmooth_has_fraction_differential_dimension
    [IsFractionRing S T] [Algebra.IsStandardSmooth R S] :
    Algebra.IsStandardSmoothOfRelativeDimension (Module.finrank T Ω[T⁄R]) R S := by
  obtain ⟨ι', σ', hσ, hι, ⟨P⟩⟩ := Algebra.IsStandardSmooth.out (R := R) (S := S)
  let : Finite σ' := hσ
  let : Finite ι' := hι
  exact P.isStandardSmoothOfRelativeDimension
    (submersive_dimension_eq_fraction_differential_finrank (T := T) P)

end

end OAI.AlgebraicGeometry.Foundations.Scheme.DifferentialRankLocalization.Algebraic
