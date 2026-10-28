import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ImmersionStalkKernel
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealBundle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrincipalPrimeDivisor

/-! # Cartier Generic Point -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.CartierGenericPoint.BundleCycles

noncomputable section

/-! An integral effective Cartier divisor has an actual
codimension-one generic point in its integral ambient scheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable {X Z : Scheme.{0}} [IsIntegral Z] (i : Z ⟶ X) [IsClosedImmersion i]

theorem integralClosedImmersion_affine_generic_ideal (U : X.Opens) (hU : IsAffineOpen U)
    (hη : i (genericPoint Z) ∈ U) :
    (hU.primeIdealOf ⟨i (genericPoint Z), hη⟩).asIdeal = RingHom.ker (i.app U).hom := by
  let V := i ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage i
  let : Nonempty V := ⟨⟨genericPoint Z, hη⟩⟩
  have h := IsAffineOpen.comap_primeIdealOf_appLE U hU V hV le_rfl (x := genericPoint Z) hη
  rw [hV.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine] at h
  have h' := congrArg PrimeSpectrum.asIdeal h
  change RingHom.ker (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom = _ at h'
  rw [Scheme.Hom.appLE_eq_app] at h'
  exact h'.symm

variable [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

theorem integralCartier_genericPoint_coheight (hi : Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals i) :
    coheight (i (genericPoint Z)) = 1 := by
  obtain ⟨U, hη, t, ht, hker⟩ := hi (i (genericPoint Z))
  let : Nonempty U.1 := ⟨⟨i (genericPoint Z), hη⟩⟩
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let q := U.2.primeIdealOf ⟨i (genericPoint Z), hη⟩
  have hq : q.asIdeal = Ideal.span {t} :=
    (integralClosedImmersion_affine_generic_ideal i U.1 U.2 hη).trans hker
  have hc : coheight (show Spec Γ(X, U.1) from q) = 1 :=
    Affine.PrincipalPrimeDivisor.BundleCycles.affinePrincipalPrime_coheight q t hq ht.ne_zero
  have ho : coheight (U.2.fromSpec (show Spec Γ(X, U.1) from q)) = coheight (show Spec Γ(X, U.1) from q) :=
    coheight_eq_of_isOpenImmersion U.2.fromSpec
  rw [U.2.fromSpec_primeIdealOf] at ho
  exact ho.trans hc

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.CartierGenericPoint.BundleCycles
