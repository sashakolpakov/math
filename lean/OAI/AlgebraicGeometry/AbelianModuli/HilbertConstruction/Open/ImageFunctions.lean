import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NonvanishingRestrictionMap

/-! # Image Functions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ImageFunctions

noncomputable section

/-! Regular functions transported through open-immersion chart isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- Pulling back a global function and then expressing it on the image open
is ordinary restriction of the original function. -/
theorem imageFunction_appTop (r : Γ(Y, ⊤)) :
    (f.appIso ⊤).inv (f.appTop r) = Y.presheaf.map (f ''ᵁ ⊤).leTop.op r := by
  have h : f.appTop ≫ (f.appIso ⊤).inv = Y.presheaf.map (f ''ᵁ ⊤).leTop.op :=
    (congrArg (fun a => a ≫ (f.appIso ⊤).inv) (f.app_eq_appLE (U := ⊤))).trans
      (f.appLE_appIso_inv (U := ⊤) (V := ⊤) (by simp))
  exact ConcreteCategory.congr_hom h r

/-- The image-open coordinate-ring isomorphisms commute with restriction. -/
theorem imageFunction_restrict (V : X.Opens) (r : Γ(X, ⊤)) :
    (f.appIso V).inv (X.presheaf.map V.leTop.op r) =
      Y.presheaf.map (f.opensFunctor.map V.leTop).op ((f.appIso ⊤).inv r) :=
  ConcreteCategory.congr_hom (f.appIso_inv_naturality V.leTop.op) r

/-- A pulled-back function expressed through two open charts is the restriction
of its image-open expression through the outer chart. -/
theorem imageFunction_iterated (g : Y ⟶ Z) [IsOpenImmersion g] (r : Γ(Y, ⊤)) :
    (g.appIso (f ''ᵁ ⊤)).inv ((f.appIso ⊤).inv (f.appTop r)) =
      Z.presheaf.map (g.opensFunctor.map (f ''ᵁ ⊤).leTop).op ((g.appIso ⊤).inv r) :=
  (congrArg (fun a : Γ(Y, f ''ᵁ ⊤) => (g.appIso (f ''ᵁ ⊤)).inv a)
    (imageFunction_appTop f r)).trans (imageFunction_restrict g (f ''ᵁ ⊤) r)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ImageFunctions
