import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PresentedMorphisms

/-! # Gluing Morphism Transfer -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.GluingMorphismTransfer

noncomputable section

/-!
# Transfer full affine gluing compatibility from modules to geometric sheaves
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Gluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PresentedMorphisms

variable {R S : CommRingCat.{u}} (i j : R ⟶ S)

/-- A specified module gluing map corresponds to a specified geometric gluing map. -/
def IsGluingSquare {M : ModuleCat.{u} R} {X : (Spec R).Modules}
    (e : (tilde.functor R).obj M ≅ X)
    (s : (ModuleCat.extendScalars i.hom).obj M ⟶ (ModuleCat.extendScalars j.hom).obj M)
    (σ : (Scheme.Modules.pullback (Spec.map i)).obj X ⟶
      (Scheme.Modules.pullback (Spec.map j)).obj X) : Prop :=
  (tilde.functor S).map s ≫ (Gluing.comparison M e j).hom = (Gluing.comparison M e i).hom ≫ σ

/-- Compatibility with the two geometric overlap maps. -/
def PreservesGeometricGluing {X Y : (Spec R).Modules} (b : X ⟶ Y)
    (σ : (Scheme.Modules.pullback (Spec.map i)).obj X ⟶
      (Scheme.Modules.pullback (Spec.map j)).obj X)
    (τ : (Scheme.Modules.pullback (Spec.map i)).obj Y ⟶
      (Scheme.Modules.pullback (Spec.map j)).obj Y) : Prop :=
  (Scheme.Modules.pullback (Spec.map i)).map b ≫ τ =
    σ ≫ (Scheme.Modules.pullback (Spec.map j)).map b

/-- Actual module compatibility transfers to actual geometric gluing compatibility. -/
theorem transfer {M N : ModuleCat.{u} R} {X Y : (Spec R).Modules}
    (eM : (tilde.functor R).obj M ≅ X) (eN : (tilde.functor R).obj N ≅ Y) (a : M ⟶ N)
    (s : (ModuleCat.extendScalars i.hom).obj M ⟶ (ModuleCat.extendScalars j.hom).obj M)
    (t : (ModuleCat.extendScalars i.hom).obj N ⟶ (ModuleCat.extendScalars j.hom).obj N)
    (σ : (Scheme.Modules.pullback (Spec.map i)).obj X ⟶
      (Scheme.Modules.pullback (Spec.map j)).obj X)
    (τ : (Scheme.Modules.pullback (Spec.map i)).obj Y ⟶
      (Scheme.Modules.pullback (Spec.map j)).obj Y)
    (hs : IsGluingSquare i j eM s σ) (ht : IsGluingSquare i j eN t τ)
    (h : (ModuleCat.extendScalars i.hom).map a ≫ t =
      s ≫ (ModuleCat.extendScalars j.hom).map a) :
    PreservesGeometricGluing i j (PresentedMorphisms.presentedMap eM eN a) σ τ :=
  GluingSquares.transfer (tilde.functor S)
    (Gluing.comparison M eM i) (Gluing.comparison M eM j) (Gluing.comparison N eN i) (Gluing.comparison N eN j)
    ((ModuleCat.extendScalars i.hom).map a) ((ModuleCat.extendScalars j.hom).map a) s t
    ((Scheme.Modules.pullback (Spec.map i)).map (PresentedMorphisms.presentedMap eM eN a))
    ((Scheme.Modules.pullback (Spec.map j)).map (PresentedMorphisms.presentedMap eM eN a)) σ τ
    (PresentedMorphisms.comparison_naturality eM eN a i) (PresentedMorphisms.comparison_naturality eM eN a j) hs ht h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.GluingMorphismTransfer
