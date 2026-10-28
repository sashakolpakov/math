import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.LocalEquations
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.ThroughSupport

/-! # Affine Factorial -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.AffineFactorial

noncomputable section

/-! Factoriality in localizations of affine charts in every smooth dimension,
including charts on disconnected presentations. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  [SmoothOfRelativeDimension m X.structureMap]

include m

theorem factorial (U : X.carrier.Opens) (hU : IsAffineOpen U) (x : U) :
    UniqueFactorizationMonoid (Localization.AtPrime (hU.primeIdealOf x).asIdeal) := by
  let q := hU.primeIdealOf x
  let S := X.carrier.presheaf.stalk (hU.fromSpec q)
  let : IsDomain S := X.stalk_isDomain _
  let : UniqueFactorizationMonoid S := LocalEquations.stalk_factorial X m _
  let e : S ≃+* Localization.AtPrime q.asIdeal :=
    (asIso (hU.fromSpec.stalkMap q)).commRingCatIsoToRingEquiv.trans
      (Spec.stalkIso Γ(X.carrier, U) q).commRingCatIsoToRingEquiv
  let : IsDomain (Localization.AtPrime q.asIdeal) := e.symm.injective.isDomain e.symm.toRingHom
  exact e.toMulEquiv.uniqueFactorizationMonoid inferInstance

theorem height_one_principal (U : X.carrier.Opens) (hU : IsAffineOpen U) (x : U) (p : PrimeSpectrum Γ(X.carrier, U))
    (hp : p.asIdeal.height = 1) :
    (p.asIdeal.map (algebraMap Γ(X.carrier, U)
      (Localization.AtPrime (hU.primeIdealOf x).asIdeal))).IsPrincipal := by
  let R := Γ(X.carrier, U)
  let q := hU.primeIdealOf x
  let T := Localization.AtPrime q.asIdeal
  let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : UniqueFactorizationMonoid T := factorial X m U hU x
  let : IsDomain T := by
    let e := (asIso (hU.fromSpec.stalkMap q)).commRingCatIsoToRingEquiv.trans
      (Spec.stalkIso Γ(X.carrier, U) q).commRingCatIsoToRingEquiv
    let := X.stalk_isDomain (hU.fromSpec q)
    exact e.symm.injective.isDomain e.symm.toRingHom
  by_cases hle : p.asIdeal ≤ q.asIdeal
  · let : (p.asIdeal.map (algebraMap R T)).IsPrime :=
      Ideal.isPrime_map_of_isLocalizationAtPrime q.asIdeal hle
    apply UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
    rw [← IsLocalization.height_under q.asIdeal.primeCompl,
      Ideal.under_map_of_isLocalizationAtPrime q.asIdeal hle, hp]
  · obtain ⟨a, ha, haq⟩ := SetLike.not_le_iff_exists.mp hle
    have ht : p.asIdeal.map (algebraMap R T) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ ha)
        (IsLocalization.map_units T (⟨a, haq⟩ : q.asIdeal.primeCompl))
    rw [ht]
    infer_instance

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.AffineFactorial
