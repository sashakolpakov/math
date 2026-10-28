import OAI.AlgebraicGeometry.Divisors.LineBundles.RegularPushoutBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Cartier Chart Base Change -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierChartBaseChange.BundleCycles

noncomputable section

/-! Affine pullback charts preserve a Cartier equation when the
closed divisor is flat over the base. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {S S' X X' Z : Scheme.{0}}
    (p : X ⟶ S) (p' : X' ⟶ S') (f : X' ⟶ X) (h : S' ⟶ S)
    (hp : IsPullback f p' p h) (i : Z ⟶ X) [IsClosedImmersion i] [Flat (i ≫ p)]
    (U : S.affineOpens) (V : X.affineOpens) (U' : S'.affineOpens)
    (hV : V.1 ≤ p ⁻¹ᵁ U.1) (hU' : U'.1 ≤ h ⁻¹ᵁ U.1)

theorem relativeCartierChart_cokernel_flat :
    (p.appLE U.1 V.1 hV ≫ i.app V.1).hom.Flat := by
  have he := Scheme.Hom.appLE_comp_appLE i p U.1 V.1 (i ⁻¹ᵁ V.1) hV le_rfl
  rw [Scheme.Hom.appLE_eq_app] at he
  rw [he]
  exact (i ≫ p).flat_appLE U.2 (V.2.preimage i) _

include hp hV hU' in
theorem relativeCartierChart_pullback_regular (t : Γ(X, V.1)) (ht : IsRegular t)
    (hk : RingHom.ker (i.app V.1).hom = Ideal.span {t}) :
    IsRegular (f.appLE V.1 (f ⁻¹ᵁ V.1 ⊓ p' ⁻¹ᵁ U'.1) inf_le_left t) := by
  let : IsIso (pushoutSection hp hU' hV rfl) :=
    isIso_pushoutSection_of_isAffineOpen hp hU' hV rfl U.2 U'.2 V.2
  have H := (isIso_pushoutSection_iff hp hU' hV rfl).mp inferInstance
  exact RegularPushoutBaseChange.BundleCycles.regular_pushout_baseChange (p.appLE U.1 V.1 hV) (h.appLE U.1 U'.1 hU')
    (f.appLE V.1 (f ⁻¹ᵁ V.1 ⊓ p' ⁻¹ᵁ U'.1) inf_le_left)
    (p'.appLE U'.1 (f ⁻¹ᵁ V.1 ⊓ p' ⁻¹ᵁ U'.1) inf_le_right) H
    (i.app V.1) (i.app_surjective V.1 V.2)
    (relativeCartierChart_cokernel_flat p i U V hV) t ht hk

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierChartBaseChange.BundleCycles
