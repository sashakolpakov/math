import OAI.AlgebraicGeometry.Picard.PoincareBundle.TildePullback

/-! # Pushforward Sections -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PushforwardSections

noncomputable section

/-!
# Global-section formulas for the actual affine direct-image comparison
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable {R S : CommRingCat.{u}}

/-- The affine direct-image comparison retains the underlying global section. -/
theorem pushforwardSectionsIso_hom_apply (f : R ⟶ S) (M : (Spec S).Modules)
    (m : (moduleSpecΓFunctor (R := S)).obj M) :
    (TildePullback.pushforwardSectionsIso f).hom.app M
        (show (moduleSpecΓFunctor (R := R)).obj
          ((Scheme.Modules.pushforward (Spec.map f)).obj M) from m) =
      (show (ModuleCat.restrictScalars f.hom).obj ((moduleSpecΓFunctor (R := S)).obj M) from m) := by
  rfl

/-- The inverse direct-image comparison likewise retains the underlying global section. -/
theorem pushforwardSectionsIso_inv_apply (f : R ⟶ S) (M : (Spec S).Modules)
    (m : (moduleSpecΓFunctor (R := S)).obj M) :
    (TildePullback.pushforwardSectionsIso f).inv.app M
        (show (ModuleCat.restrictScalars f.hom).obj ((moduleSpecΓFunctor (R := S)).obj M) from m) =
      (show (moduleSpecΓFunctor (R := R)).obj
        ((Scheme.Modules.pushforward (Spec.map f)).obj M) from m) := by
  rfl

variable {T : CommRingCat.{u}}

/-- Compare sections after two direct images, using the two affine comparison maps in succession. -/
def iteratedSectionsIso (f : R ⟶ S) (g : S ⟶ T) :
    Scheme.Modules.pushforward (Spec.map g) ⋙ Scheme.Modules.pushforward (Spec.map f) ⋙
        moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := T) ⋙ ModuleCat.restrictScalars (f ≫ g).hom :=
  Functor.isoWhiskerLeft (Scheme.Modules.pushforward (Spec.map g))
      (TildePullback.pushforwardSectionsIso f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (TildePullback.pushforwardSectionsIso g)
      (ModuleCat.restrictScalars f.hom) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleSpecΓFunctor (R := T))
      (ModuleCat.restrictScalarsComp f.hom g.hom).symm

/-- Compare the same sections using the geometric composite morphism and one affine comparison. -/
def compositeSectionsIso (f : R ⟶ S) (g : S ⟶ T) :
    Scheme.Modules.pushforward (Spec.map g) ⋙ Scheme.Modules.pushforward (Spec.map f) ⋙
        moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := T) ⋙ ModuleCat.restrictScalars (f ≫ g).hom :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Scheme.Modules.pushforwardComp (Spec.map g) (Spec.map f) ≪≫
        Scheme.Modules.pushforwardCongr (Spec.map_comp f g).symm)
      (moduleSpecΓFunctor (R := R)) ≪≫
    TildePullback.pushforwardSectionsIso (f ≫ g)

/-- The iterated comparison retains the actual global section. -/
theorem iteratedSectionsIso_hom_apply (f : R ⟶ S) (g : S ⟶ T) (M : (Spec T).Modules)
    (m : (moduleSpecΓFunctor (R := T)).obj M) :
    (iteratedSectionsIso f g).hom.app M
        (show ((Scheme.Modules.pushforward (Spec.map g) ⋙ Scheme.Modules.pushforward (Spec.map f) ⋙
          moduleSpecΓFunctor (R := R)).obj M) from m) =
      (show (ModuleCat.restrictScalars (f ≫ g).hom).obj
        ((moduleSpecΓFunctor (R := T)).obj M) from m) := rfl

/-- The composite comparison retains the same actual global section. -/
theorem compositeSectionsIso_hom_apply (f : R ⟶ S) (g : S ⟶ T) (M : (Spec T).Modules)
    (m : (moduleSpecΓFunctor (R := T)).obj M) :
    (compositeSectionsIso f g).hom.app M
        (show ((Scheme.Modules.pushforward (Spec.map g) ⋙ Scheme.Modules.pushforward (Spec.map f) ⋙
          moduleSpecΓFunctor (R := R)).obj M) from m) =
      (show (ModuleCat.restrictScalars (f ≫ g).hom).obj
        ((moduleSpecΓFunctor (R := T)).obj M) from m) := by
  change M.presheaf.map (𝟙 (op ⊤)) m = m
  rw [M.presheaf.map_id]
  rfl

/-- The affine direct-image/global-sections isomorphism is compatible with composition. -/
theorem sectionsIso_composition (f : R ⟶ S) (g : S ⟶ T) :
    compositeSectionsIso f g = iteratedSectionsIso f g := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  exact (compositeSectionsIso_hom_apply f g M m).trans (iteratedSectionsIso_hom_apply f g M m).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PushforwardSections
