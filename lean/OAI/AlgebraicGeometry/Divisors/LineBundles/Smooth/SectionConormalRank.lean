import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.ConormalFinite
import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.RelativeDifferentialRank

/-! # Section Conormal Rank -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.SectionConormalRank.BundleCycles

noncomputable section

/-! The actual conormal rank of a smooth algebra section is the relative
differential rank at its image prime. -/

open KaehlerDifferential

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]
    [IsScalarTower A B A] [Algebra.Smooth A B]

theorem smoothSectionConormal_rankAtStalk (p : PrimeSpectrum A) :
    Module.rankAtStalk (R := A) (RingHom.ker (algebraMap B A)).Cotangent p =
      Module.rankAtStalk Ω[B⁄A] (p.comap (algebraMap B A)) := by
  let : Module.Finite A (RingHom.ker (algebraMap B A)).Cotangent := Section.ConormalFinite.BundleCycles.sectionConormal_finite A B
  have H := congrFun (Module.rankAtStalk_eq_of_equiv (SectionCotangent.BundleCycles.smoothSectionCotangentEquiv A B)) p
  exact H.trans (Module.rankAtStalk_baseChange (R := B) (M := Ω[B⁄A]) p)

theorem smoothSectionConormal_rank_of_relativeDimension (n : ℕ)
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap A B))
    (p : PrimeSpectrum A) :
    Module.rankAtStalk (R := A) (RingHom.ker (algebraMap B A)).Cotangent p = n :=
  (smoothSectionConormal_rankAtStalk A B p).trans
    (RelativeDifferentialRank.BundleCycles.locallyStandardSmooth_differential_rank A B n h (p.comap (algebraMap B A)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.SectionConormalRank.BundleCycles
