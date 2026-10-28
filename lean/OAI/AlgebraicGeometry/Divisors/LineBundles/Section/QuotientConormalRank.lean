import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.SectionConormalRank
import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.QuotientProjective
import OAI.AlgebraicGeometry.Divisors.LineBundles.ScalarSurjectionModuleRank

/-! # Quotient Conormal Rank -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Section.QuotientConormalRank.BundleCycles

noncomputable section

/-! The conormal module over the actual section quotient has precisely
the smooth relative rank at every prime of that quotient. -/

theorem sectionQuotientConormal_rank_of_relativeDimension
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra B A]
    [IsScalarTower A B A] [Algebra.Smooth A B] (n : ℕ)
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap A B))
    (q : PrimeSpectrum (B ⧸ RingHom.ker (algebraMap B A))) :
    Module.rankAtStalk (R := B ⧸ RingHom.ker (algebraMap B A)) (RingHom.ker (algebraMap B A)).Cotangent q = n := by
  let Q := B ⧸ RingHom.ker (algebraMap B A)
  let M := (RingHom.ker (algebraMap B A)).Cotangent
  let e := ConormalBasis.BundleCycles.sectionQuotientEquiv A B
  let : Algebra Q A := e.toRingHom.toAlgebra
  let : IsScalarTower Q A M := IsScalarTower.of_algebraMap_smul (fun a m => by
    have H := ConormalBasis.BundleCycles.sectionQuotientEquiv_smul A B (e a) m
    rw [e.symm_apply_apply] at H
    exact H.symm)
  let : Module.Finite Q M := QuotientProjective.BundleCycles.sectionQuotientConormal_finite A B
  let : Module.Projective Q M := QuotientProjective.BundleCycles.sectionQuotientConormal_projective A B
  let p : PrimeSpectrum A := q.comap e.symm.toRingHom
  have hp : p.comap (algebraMap Q A) = q := by
    apply PrimeSpectrum.ext
    change Ideal.comap e.toRingHom (Ideal.comap e.symm.toRingHom q.asIdeal) = q.asIdeal
    rw [Ideal.comap_comap]
    have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id Q := by
      ext a
      exact e.symm_apply_apply a
    rw [he, Ideal.comap_id]
  have H := ScalarSurjectionModuleRank.BundleCycles.moduleRankAtStalk_surjectiveScalars Q A M e.surjective p
  rw [hp] at H
  exact H.symm.trans (LineBundles.Smooth.SectionConormalRank.BundleCycles.smoothSectionConormal_rank_of_relativeDimension A B n h p)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Section.QuotientConormalRank.BundleCycles
