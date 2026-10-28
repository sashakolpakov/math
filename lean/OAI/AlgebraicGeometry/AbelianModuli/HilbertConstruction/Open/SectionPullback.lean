import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionUnits

/-! # Section Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SectionPullback

noncomputable section

/-! Pull regular functions to arbitrary subopens of an inverse image, with the two restriction compatibilities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def openSectionPullback (W : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ W) : Γ(Y, W) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom.comp (f.app W).hom

theorem openSectionPullback_restrict_target (W : Y.Opens) (V Z : X.Opens)
    (h : V ≤ f ⁻¹ᵁ W) (a : Z ≤ V) (r : Γ(Y, W)) :
    X.presheaf.map (homOfLE a).op (openSectionPullback f W V h r) =
      openSectionPullback f W Z (a.trans h) r :=
  Relative.OpenFunctionUnits.openFunction_restriction_comp h a (f.app W r)

theorem openSectionPullback_restrict_source (W Z : Y.Opens) (a : Z ≤ W) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ Z) (r : Γ(Y, W)) :
    openSectionPullback f W V (h.trans ((TopologicalSpace.Opens.map f.base).monotone a)) r =
      openSectionPullback f Z V h (Y.presheaf.map (homOfLE a).op r) := by
  have he := ConcreteCategory.congr_hom (f.naturality (homOfLE a).op) r
  exact (Relative.OpenFunctionUnits.openFunction_restriction_comp ((TopologicalSpace.Opens.map f.base).monotone a) h (f.app W r)).symm.trans
    (congrArg (X.presheaf.map (homOfLE h).op) he.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SectionPullback
