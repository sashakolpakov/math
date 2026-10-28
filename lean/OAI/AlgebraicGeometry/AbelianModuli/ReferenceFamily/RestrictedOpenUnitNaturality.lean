import Mathlib.AlgebraicGeometry.Restrict

/-! # Restricted Open Unit Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RestrictedOpenUnitNaturality

noncomputable section

/-! Actual maps between corresponding open subschemes commute
with restriction of invertible regular functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U V : Y.Opens} {U' V' : X.Opens} (h : V ≤ U) (h' : V' ≤ U')
    (rU : U'.toScheme ⟶ U.toScheme) (rV : V'.toScheme ⟶ V.toScheme)
    (hu : rU ≫ U.ι = U'.ι ≫ f) (hv : rV ≫ V.ι = V'.ι ≫ f)

include hu hv in
theorem openMaps_restriction : rV ≫ Y.homOfLE h = X.homOfLE h' ≫ rU := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, Scheme.homOfLE_ι, hv, Category.assoc, hu,
    ← Category.assoc, Scheme.homOfLE_ι]

include hu hv in
theorem openUnits_restriction (a : Γ(U.toScheme, ⊤)ˣ) :
    Units.map rV.appTop.hom.toMonoidHom (Units.map (Y.homOfLE h).appTop.hom.toMonoidHom a) =
      Units.map (X.homOfLE h').appTop.hom.toMonoidHom (Units.map rU.appTop.hom.toMonoidHom a) := by
  apply Units.ext
  exact congrArg (fun g : V'.toScheme ⟶ U.toScheme => g.appTop a.val)
    (openMaps_restriction f h h' rU rV hu hv)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RestrictedOpenUnitNaturality
