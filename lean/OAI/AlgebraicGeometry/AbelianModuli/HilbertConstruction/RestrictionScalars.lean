import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

/-! # Restriction Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionScalars

noncomputable section

/-! Restriction of scalar endomorphisms and independence from a chosen structure-module frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- The scalar of an endomorphism on an open is the restriction of its global scalar. -/
theorem structureModuleEndValue_onOpen (a : End (Line.Bundles.structureModule X)) (U : X.Opens) :
    a.app U (1 : Γ(X, U)) =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (Frame.Coordinates.structureModuleEndValue X a) := by
  have ha := ConcreteCategory.congr_hom
    (a.mapPresheaf.naturality (homOfLE (show U ≤ ⊤ from le_top)).op) (1 : Γ(X, ⊤))
  change a.app U (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (1 : Γ(X, ⊤))) = _ at ha
  exact (congrArg (fun z : Γ(X, U) => a.app U z)
    (map_one (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom)).symm.trans ha

/-- On an open immersion, restricting to the image and then using the structure-sheaf isomorphism
is the map on global functions. -/
theorem appIso_top_restrict (f : X ⟶ Y) [IsOpenImmersion f] (r : Γ(Y, ⊤)) :
    (f.appIso ⊤).hom (Y.presheaf.map (homOfLE (show f ''ᵁ ⊤ ≤ ⊤ from le_top)).op r) =
      f.appTop r := by
  have hh := f.map_appLE (Scheme.Hom.preimage_image_eq f ⊤).ge
    (homOfLE (show f ''ᵁ ⊤ ≤ ⊤ from le_top)).op
  rw [← f.appIso_hom'] at hh
  have he : f.appLE ⊤ ⊤ (by intro x _; trivial) = f.appTop := by
    change f.appTop ≫ X.presheaf.map (𝟙 (Opposite.op (⊤ : X.Opens))) = f.appTop
    exact (congrArg (fun z : Γ(X, ⊤) ⟶ Γ(X, ⊤) => f.appTop ≫ z)
      (X.presheaf.map_id (Opposite.op (⊤ : X.Opens)))).trans (Category.comp_id f.appTop)
  exact (ConcreteCategory.congr_hom hh r).trans (ConcreteCategory.congr_hom he r)

/-- Conjugating a restricted scalar map through any frame gives the pulled-back global scalar. -/
theorem structureModuleEndValue_restrict (f : X ⟶ Y) [IsOpenImmersion f]
    (a : End (Line.Bundles.structureModule Y)) (e : (Line.Bundles.structureModule Y).restrict f ≅ Line.Bundles.structureModule X) :
    Frame.Coordinates.structureModuleEndValue X (e.inv ≫ (Scheme.Modules.restrictFunctor f).map a ≫ e.hom) =
      f.appTop (Frame.Coordinates.structureModuleEndValue Y a) := by
  let U : X.Opens := ⊤
  let V : Y.Opens := f ''ᵁ U
  let c : Γ(Y, V) := a.app V (1 : Γ(Y, V))
  let b : Γ(Y, V) := e.inv.app U (1 : Γ(X, U))
  let q : Γ(X, U) := (f.appIso U).hom c
  have hcb : q • (show Γ((Line.Bundles.structureModule Y).restrict f, U) from b) = c * b := by
    change (f.appIso U).inv ((f.appIso U).hom c) * b = c * b
    exact congrArg (fun z : Γ(Y, V) => z * b)
      (ConcreteCategory.congr_hom (f.appIso U).hom_inv_id c)
  have heb : e.hom.app U b = (1 : Γ(X, U)) :=
    ConcreteCategory.congr_hom
      (congrArg (fun z : Line.Bundles.structureModule X ⟶ Line.Bundles.structureModule X => z.app U) e.inv_hom_id)
      (1 : Γ(X, U))
  have hec : e.hom.app U (c * b) = q :=
    (congrArg (fun z : Γ((Line.Bundles.structureModule Y).restrict f, U) => e.hom.app U z) hcb).symm.trans
      ((e.hom.app_smul q b).trans
        ((congrArg (fun z : Γ(X, U) => q * z) heb).trans (mul_one q)))
  have ha : a.app V b = c * b := (TensorPower.Units.structureModuleEnd_app a V b).trans (mul_comm b c)
  have hval : Frame.Coordinates.structureModuleEndValue X
      (e.inv ≫ (Scheme.Modules.restrictFunctor f).map a ≫ e.hom) = q :=
    (congrArg (fun z : Γ((Line.Bundles.structureModule Y).restrict f, U) => e.hom.app U z) ha).trans hec
  exact hval.trans
    ((congrArg (fun z : Γ(Y, V) => (f.appIso U).hom z) (structureModuleEndValue_onOpen a V)).trans
      (appIso_top_restrict f (Frame.Coordinates.structureModuleEndValue Y a)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionScalars
