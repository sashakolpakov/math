import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.OpenUnits
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RestrictedOpenUnitNaturality

/-! # Open Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.OpenRestriction

noncomputable section

/-! The actual open diagrams and their limit projections commute
with open inclusion, retaining the original restriction of regular units. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

theorem opensConeProjection_ι (i : I) (U : (D.obj i).Opens) (k : Over i) :
    (opensCone D c i U).π.app k ≫ (D.map k.hom ⁻¹ᵁ U).ι =
      (c.π.app i ⁻¹ᵁ U).ι ≫ c.π.app k.left :=
  Scheme.Hom.resLE_comp_ι _ _

theorem opensDiagramMap_ι {i : I} (U : (D.obj i).Opens) {k l : Over i} (f : k ⟶ l) :
    (opensDiagram D i U).map f ≫ (D.map l.hom ⁻¹ᵁ U).ι =
      (D.map k.hom ⁻¹ᵁ U).ι ≫ D.map f.left :=
  Scheme.Hom.resLE_comp_ι _ _

theorem opensConeUnits_restriction {i : I} {U V : (D.obj i).Opens} (h : V ≤ U) (k : Over i)
    (a : Γ((opensDiagram D i U).obj k, ⊤)ˣ) :
    Units.map ((opensCone D c i V).π.app k).appTop.hom.toMonoidHom
      (Units.map ((D.obj k.left).homOfLE (show D.map k.hom ⁻¹ᵁ V ≤ D.map k.hom ⁻¹ᵁ U
        from fun _ hx => h hx)).appTop.hom.toMonoidHom a) =
      Units.map (c.pt.homOfLE (show c.π.app i ⁻¹ᵁ V ≤ c.π.app i ⁻¹ᵁ U
        from fun _ hx => h hx)).appTop.hom.toMonoidHom
          (Units.map ((opensCone D c i U).π.app k).appTop.hom.toMonoidHom a) :=
  RestrictedOpenUnitNaturality.openUnits_restriction (c.π.app k.left) (fun _ hx => h hx) (fun _ hx => h hx)
    ((opensCone D c i U).π.app k) ((opensCone D c i V).π.app k)
    (opensConeProjection_ι D c i U k) (opensConeProjection_ι D c i V k) a

theorem opensDiagramUnits_restriction {i : I} {U V : (D.obj i).Opens} (h : V ≤ U)
    {k l : Over i} (f : k ⟶ l) (a : Γ((opensDiagram D i U).obj l, ⊤)ˣ) :
    Units.map ((opensDiagram D i V).map f).appTop.hom.toMonoidHom
      (Units.map ((D.obj l.left).homOfLE (show D.map l.hom ⁻¹ᵁ V ≤ D.map l.hom ⁻¹ᵁ U
        from fun _ hx => h hx)).appTop.hom.toMonoidHom a) =
      Units.map ((D.obj k.left).homOfLE (show D.map k.hom ⁻¹ᵁ V ≤ D.map k.hom ⁻¹ᵁ U
        from fun _ hx => h hx)).appTop.hom.toMonoidHom
          (Units.map ((opensDiagram D i U).map f).appTop.hom.toMonoidHom a) :=
  RestrictedOpenUnitNaturality.openUnits_restriction (D.map f.left) (fun _ hx => h hx) (fun _ hx => h hx)
    ((opensDiagram D i U).map f) ((opensDiagram D i V).map f)
    (opensDiagramMap_ι D U f) (opensDiagramMap_ι D V f) a

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.OpenRestriction
