import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.GermNaturality
import Mathlib.AlgebraicGeometry.Stalk

/-! # Point Coefficients -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.PointCoefficients

noncomputable section

/-! Coefficient specialization at a local-ring-valued scheme point factors
through the actual local ring at its closed point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X : Scheme.{u}} {R : Type u} [CommRing R] [IsLocalRing R]

def schemePointCoefficientMap (f : Spec (CommRingCat.of R) ⟶ X) : Γ(X, ⊤) →+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp f.appTop.hom

theorem schemePointCoefficientMap_stalk (f : Spec (CommRingCat.of R) ⟶ X) :
    schemePointCoefficientMap f = (Scheme.stalkClosedPointTo f).hom.comp
      (X.presheaf.Γgerm (f (IsLocalRing.closedPoint R))).hom := by
  ext s
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom (f.appTop s) =
    (stalkClosedPointIso (CommRingCat.of R)).hom
      (f.stalkMap (IsLocalRing.closedPoint R) (X.presheaf.Γgerm (f (IsLocalRing.closedPoint R)) s))
  have he := congrArg (fun r => (stalkClosedPointIso (CommRingCat.of R)).hom r)
    (Global.GermNaturality.global_germ_appTop f (IsLocalRing.closedPoint R) s)
  exact (ConcreteCategory.congr_hom (germ_stalkClosedPointIso_hom (CommRingCat.of R))
    (f.appTop s)).symm.trans he.symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.PointCoefficients
