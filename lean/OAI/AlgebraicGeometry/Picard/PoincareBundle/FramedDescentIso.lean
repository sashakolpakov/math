import OAI.AlgebraicGeometry.Picard.Homomorphisms.FramedDescentMorphisms

/-! # Framed Descent Iso -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedDescentIso

noncomputable section

/-! Actual isomorphisms of framed descent data preserve their character scalars. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.Homomorphisms.FramedDescentMorphisms.Construction

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (D E : Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent f)
  (a : D.module ≅ E.module) (e : D.module ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)

/-- Transporting the global frame through an actual descent isomorphism preserves every native scalar. -/
theorem scalar_eq {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q)
    (h : (Scheme.Modules.pullback x).map a.hom ≫ E.hom q x y hx hy =
      D.hom q x y hx hy ≫ (Scheme.Modules.pullback y).map a.hom) :
    Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar E (a.symm ≪≫ e) q x y hx hy = Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar D e q x y hx hy := by
  have hm := Homomorphisms.FramedDescentMorphisms.Construction.framedDescent_morphism D E e (a.symm ≪≫ e) a.hom q x y hx hy h
  have hu : e.inv ≫ a.hom ≫ (a.symm ≪≫ e).hom = 𝟙 _ := by
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc, Iso.inv_hom_id]
  rw [hu] at hm
  have hid (z : T ⟶ X) : Homomorphisms.UnitPullbackScalars.Construction.unitEndPullback z (𝟙 (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) = 𝟙 _ := by
    change (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso z).inv ≫ (Scheme.Modules.pullback z).map (𝟙 (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) ≫
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso z).hom = 𝟙 _
    rw [(Scheme.Modules.pullback z).map_id (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X), Category.id_comp, Iso.inv_hom_id]
  rw [hid x, hid y, Category.id_comp, Category.comp_id] at hm
  exact congrArg (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T) hm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedDescentIso
