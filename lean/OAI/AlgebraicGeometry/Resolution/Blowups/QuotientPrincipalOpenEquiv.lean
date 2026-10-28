import OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.PrincipalOpenLift
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ComponentBaseChange

/-! # Quotient Principal Open Equiv -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.QuotientPrincipalOpenEquiv.Construction

noncomputable section

/-! Actual normal quotients on principal ambient opens agree with the corresponding quotient opens. -/

universe u

variable (k : Type u) [CommRing k] {R : Type u} [CommRing R] [Algebra k R]

def normalQuotientPrincipalOpenEquiv (z r : R) :
    (Localization.Away r ⧸ Ideal.span {algebraMap R (Localization.Away r) z}) ≃ₐ[k]
      Localization.Away (Ideal.Quotient.mk (Ideal.span {z}) r) := by
  let q : R →ₐ[k] R ⧸ Ideal.span {z} := Ideal.Quotient.mkₐ k _
  let q' := Blowups.Quotient.PrincipalOpenLift.Construction.quotientPrincipalOpenMap q r
  have hker : RingHom.ker q'.toRingHom = Ideal.span {algebraMap R (Localization.Away r) z} := by
    have hq : RingHom.ker q.toRingHom = Ideal.span {z} := Ideal.mk_ker
    rw [Blowups.Quotient.PrincipalOpenLift.Construction.quotientPrincipalOpenMap_kernel, hq, Ideal.map_span, Set.image_singleton]
  exact (Ideal.quotientEquivAlgOfEq k hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (Blowups.Quotient.PrincipalOpenLift.Construction.quotientPrincipalOpenMap_surjective q Ideal.Quotient.mk_surjective r))

theorem normalQuotientPrincipalOpenEquiv_mk (z r : R) (a : Localization.Away r) :
    normalQuotientPrincipalOpenEquiv k z r (Ideal.Quotient.mk _ a) =
      Blowups.Quotient.PrincipalOpenLift.Construction.quotientPrincipalOpenMap (Ideal.Quotient.mkₐ k (Ideal.span {z})) r a := by
  let q : R →ₐ[k] R ⧸ Ideal.span {z} := Ideal.Quotient.mkₐ k _
  have hker : RingHom.ker (Blowups.Quotient.PrincipalOpenLift.Construction.quotientPrincipalOpenMap q r).toRingHom =
      Ideal.span {algebraMap R (Localization.Away r) z} := by
    have hq : RingHom.ker q.toRingHom = Ideal.span {z} := Ideal.mk_ker
    rw [Blowups.Quotient.PrincipalOpenLift.Construction.quotientPrincipalOpenMap_kernel, hq, Ideal.map_span, Set.image_singleton]
  have hq := Blowups.Quotient.PrincipalOpenLift.Construction.quotientPrincipalOpenMap_surjective q Ideal.Quotient.mk_surjective r
  change Ideal.quotientKerAlgEquivOfSurjective hq
    (Ideal.quotientEquivAlgOfEq k hker.symm
      (Ideal.Quotient.mk (Ideal.span {algebraMap R (Localization.Away r) z}) a)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk hq a

theorem normalQuotientPrincipalOpenEquiv_aligned (z r : R) :
    (normalQuotientPrincipalOpenEquiv k z r).toAlgHom.comp
      (Coefficient.TangentNaturality.Construction.alignedHypersurfaceAlgHom (IsScalarTower.toAlgHom k R (Localization.Away r))
        z (algebraMap R (Localization.Away r) z) rfl) =
      IsScalarTower.toAlgHom k (R ⧸ Ideal.span {z})
        (Localization.Away (Ideal.Quotient.mk (Ideal.span {z}) r)) := by
  apply AlgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change normalQuotientPrincipalOpenEquiv k z r
    (Ideal.Quotient.mk _ (algebraMap R (Localization.Away r) a)) = _
  rw [normalQuotientPrincipalOpenEquiv_mk, Blowups.Quotient.PrincipalOpenLift.Construction.quotientPrincipalOpenMap_constants]
  rfl

theorem homogenized_coefficient_map_principal_quotient [Algebra.Smooth k R]
    (z r : R) (J : Ideal R) (n : ℕ) :
    (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (algebraMap R (Localization.Away r) z)
      (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k (J.map (algebraMap R (Localization.Away r))) n) (n + 1)).map
      (normalQuotientPrincipalOpenEquiv k z r).toRingHom =
    (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)).map
      (algebraMap (R ⧸ Ideal.span {z}) (Localization.Away (Ideal.Quotient.mk (Ideal.span {z}) r))) := by
  let f : R →ₐ[k] Localization.Away r := IsScalarTower.toAlgHom k R _
  have hf : f.toRingHom.Etale := RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway r)
  have he := Coefficient.ComponentBaseChange.Construction.smooth_relativeCoefficientIdeal_map_aligned k f hf z (f z) rfl
    (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)
  rw [Coefficient.ComponentBaseChange.Construction.smooth_relativeHomogenizedIdeal_map k f hf] at he
  change (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)).map
    (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap (algebraMap R (Localization.Away r)) z
      (algebraMap R (Localization.Away r) z) rfl) =
    Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (algebraMap R (Localization.Away r) z)
      (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k (J.map (algebraMap R (Localization.Away r))) n) (n + 1) at he
  rw [← he, Ideal.map_map]
  exact congrArg (Ideal.map · _) (congrArg AlgHom.toRingHom (normalQuotientPrincipalOpenEquiv_aligned k z r))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.QuotientPrincipalOpenEquiv.Construction
