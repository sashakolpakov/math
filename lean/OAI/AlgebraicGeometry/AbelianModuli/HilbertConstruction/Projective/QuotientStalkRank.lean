import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ProjectiveQuotientRank
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Quotient Stalk Rank -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.QuotientStalkRank

noncomputable section

/-! Additivity of stalk ranks for a projective quotient is obtained
from an actual direct-sum decomposition. It holds over arbitrary
coefficient rings, without reducing them or passing to field points. -/
universe u v
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.Finite R M] [Module.Projective R M]

theorem projectiveQuotient_rankAtStalk_add (P : Submodule R M)
    [Module.Projective R (M ⧸ P)] (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) (M ⧸ P) p + Module.rankAtStalk (R := R) P p =
      Module.rankAtStalk (R := R) M p := by
  obtain ⟨r, hr⟩ := HilbertScheme.Presentations.Projective.QuotientRetraction.exists_projective_quotient_retraction P
  have hsurj : Function.Surjective r := fun x => ⟨x.val, LinearMap.congr_fun hr x⟩
  have : Module.Finite R P := Module.Finite.of_surjective r hsurj
  have : Module.Projective R P := Module.Projective.of_split P.subtype r hr
  have hc : IsCompl P r.ker := LinearMap.isCompl_of_proj (fun x => LinearMap.congr_fun hr x)
  let e := P.quotientEquivOfIsCompl r.ker hc
  have : Module.Finite R r.ker := Module.Finite.equiv e
  have : Module.Projective R r.ker := Module.Projective.of_equiv e
  have h := congrFun (Module.rankAtStalk_eq_of_equiv (P.prodEquivOfIsCompl r.ker hc)) p
  rw [Module.rankAtStalk_prod, Pi.add_apply,
    ← congrFun (Module.rankAtStalk_eq_of_equiv e) p] at h
  exact (Nat.add_comm _ _).trans h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.QuotientStalkRank
