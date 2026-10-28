import OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalIdealSheaf
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.Data

/-! # Principal Regular -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalRegular.Construction

noncomputable section

/-! Nonzero locally principal ideals on integral schemes have regular actual local generators. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem locallyPrincipal_regular_generators
    {X : Scheme.{u}} [IsIntegral X] (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (hlocal : PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf I) (x : X) :
    ∃ (U : X.affineOpens), x ∈ U.1 ∧ ∃ r : Γ(X, U), IsRegular r ∧ I.ideal U = Ideal.span {r} := by
  obtain ⟨U, hx, r, hr⟩ := hlocal x
  let : Nonempty U.1 := ⟨⟨x, hx⟩⟩
  have hr0 : r ≠ 0 := by
    intro hz
    apply Blowup.BlowupRestriction.Construction.nonzero_idealSheaf_on_affineOpen I hI U
    rw [hr, hz, Ideal.span_singleton_eq_bot.mpr rfl]
  exact ⟨U, hx, r, IsRegular.of_ne_zero hr0, hr⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Locally.PrincipalRegular.Construction
