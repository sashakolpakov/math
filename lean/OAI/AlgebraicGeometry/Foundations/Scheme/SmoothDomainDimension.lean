import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothComplexPoint
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Smooth Domain Dimension -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic

noncomputable section

/-!
# A common dimension for standard smooth charts of an integral affine algebra

The dimension is the rank of the actual Kähler differential module at the
zero prime. For a smooth algebra that is a domain, finite flatness makes
this rank constant at all primes. Base change for Kähler differentials then
identifies every nonempty standard smooth localization with this same rank.
-/

universe u v w t

section FiniteFlat

variable {S : Type v} [CommRing S] [IsDomain S]
variable (M : Type w) [AddCommGroup M] [Module S M]
variable [Module.Finite S M] [Module.Flat S M]

/-- A finite flat module over a domain has the same rank at all prime stalks.
The proof compares both primes to the zero prime. -/
theorem finiteFlat_rankAtStalk_eq (p q : PrimeSpectrum S) :
    Module.rankAtStalk M p = Module.rankAtStalk M q := by
  let z : PrimeSpectrum S := ⟨⊥, inferInstance⟩
  have hz (r : PrimeSpectrum S) : z ≤ r := by
    change (⊥ : Ideal S) ≤ r.asIdeal
    exact bot_le
  exact (Module.rankAtStalk_eq_of_le_of_finite_of_flat M (hz p)).symm.trans
    (Module.rankAtStalk_eq_of_le_of_finite_of_flat M (hz q))

end FiniteFlat

section DifferentialRank

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] [IsDomain S]

/-- The rank of the relative Kähler differential module at the generic point. -/
def genericDifferentialRank : ℕ :=
  Module.rankAtStalk Ω[S⁄R] (⟨⊥, inferInstance⟩ : PrimeSpectrum S)

variable {R S}

/-- Smoothness supplies finite flatness, so the generic rank equals the rank
at every prime of this integral affine algebra. -/
theorem kaehler_rankAtStalk_eq_generic [Algebra.Smooth R S] (p : PrimeSpectrum S) :
    Module.rankAtStalk Ω[S⁄R] p = genericDifferentialRank R S :=
  finiteFlat_rankAtStalk_eq Ω[S⁄R] p ⟨⊥, inferInstance⟩

end DifferentialRank

section PresentationStalk

variable {R : Type u} {T : Type v} [CommRing R] [CommRing T] [Algebra R T]
variable [Nontrivial T] {ι : Type w} {σ : Type t} [Finite ι] [Finite σ]

/-- The dimension of a submersive presentation is the rank at every stalk of
its actual differential module. -/
theorem submersive_dimension_eq_rankAtStalk
    (P : Algebra.SubmersivePresentation R T ι σ) (p : PrimeSpectrum T) :
    P.dimension = Module.rankAtStalk Ω[T⁄R] p := by
  let : Module.Free T Ω[T⁄R] := P.free_kaehlerDifferential
  have hfin : Module.finrank T Ω[T⁄R] = P.dimension :=
    Module.finrank_eq_of_rank_eq P.rank_kaehlerDifferential
  have hstalk : Module.rankAtStalk Ω[T⁄R] p = Module.finrank T Ω[T⁄R] := by
    simp
  exact hfin.symm.trans hstalk.symm

end PresentationStalk

section Localization

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable [Algebra S T] [IsScalarTower R S T] [IsDomain S] [Nontrivial T]
variable [Algebra.Smooth R S] (W : Submonoid S) [IsLocalization W T]
variable {ι σ : Type*} [Finite ι] [Finite σ]

include W in
/-- Every submersive presentation of a nonzero localization of a smooth domain
has the same dimension, measured on the original differential module. -/
theorem localized_submersive_dimension
    (P : Algebra.SubmersivePresentation R T ι σ) :
    P.dimension = genericDifferentialRank R S := by
  let : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_isLocalization W
  let p : PrimeSpectrum T := Classical.choice inferInstance
  calc
    P.dimension = Module.rankAtStalk Ω[T⁄R] p :=
      submersive_dimension_eq_rankAtStalk P p
    _ = Module.rankAtStalk Ω[S⁄R] (p.comap (algebraMap S T)) :=
      Module.rankAtStalk_isBaseChange (KaehlerDifferential.isBaseChange_of_formallyEtale R S T) p
    _ = genericDifferentialRank R S := kaehler_rankAtStalk_eq_generic _

end Localization

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsDomain S] [Algebra.Smooth R S]

/-- A nonempty standard smooth principal localization of an integral smooth
algebra has relative dimension equal to its generic differential rank. -/
theorem standardSmoothAway_has_genericDimension (g : S) (hg : g ≠ 0)
    [Algebra.IsStandardSmooth R (Localization.Away g)] :
    Algebra.IsStandardSmoothOfRelativeDimension (genericDifferentialRank R S)
      R (Localization.Away g) := by
  let : IsDomain (Localization.Away g) := Localization.Away.isDomain hg
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ :=
    Algebra.IsStandardSmooth.out (R := R) (S := Localization.Away g)
  let : Finite σ := hσ
  let : Finite ι := hι
  exact P.isStandardSmoothOfRelativeDimension
    (localized_submersive_dimension (R := R) (S := S) (Submonoid.powers g) P)

/-- A single natural number works for all nonempty standard smooth principal
charts. Equality of chart dimensions is proved, not required as input. -/
theorem smooth_domain_exists_common_dimension :
    ∃ n : ℕ, ∀ g : S, g ≠ 0 →
      Algebra.IsStandardSmooth R (Localization.Away g) →
      Algebra.IsStandardSmoothOfRelativeDimension n R (Localization.Away g) := by
  refine ⟨genericDifferentialRank R S, ?_⟩
  intro g hg hstd
  let : Algebra.IsStandardSmooth R (Localization.Away g) := hstd
  exact standardSmoothAway_has_genericDimension g hg

end

end OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic
