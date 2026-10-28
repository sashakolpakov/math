import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.DiagramGluedStructure
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramGluedIsomorphisms

/-! # Equifibered Glued Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EquifiberedGluedIsomorphism

noncomputable section

/-! A Cartesian diagram isomorphism glues to an isomorphism over the base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

variable {C : Type u} [CommRing C] {J : Type v} [Category J] [Quiver.IsThin J] [Small.{u} J]
variable {F G : J ⥤ Over (Spec (.of C))} (q : F ⟶ G) (hq : q.Equifibered)
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (G.map h).left]
variable [((G ⋙ Over.forget (Spec (.of C))) ⋙ Scheme.forget).IsLocallyDirected]
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (F.map h).left]
variable [((F ⋙ Over.forget (Spec (.of C))) ⋙ Scheme.forget).IsLocallyDirected]

local instance {i j : J} (h : i ⟶ j) : IsOpenImmersion ((F ⋙ Over.forget (Spec (.of C))).map h) :=
  inferInstanceAs (IsOpenImmersion (F.map h).left)

local instance {i j : J} (h : i ⟶ j) : IsOpenImmersion ((G ⋙ Over.forget (Spec (.of C))).map h) :=
  inferInstanceAs (IsOpenImmersion (G.map h).left)

theorem equifiberedOverGluedMorphism_isIso [IsIso q] :
    IsIso (Closed.DiagramGluedStructure.equifiberedOverGluedMorphism q hq) := by
  have he : Closed.DiagramGluedStructure.equifiberedOverGluedMorphism q hq = (DiagramGluedIsomorphisms.diagramGluedOverIso (asIso q)).hom := by
    apply Over.OverMorphism.ext
    apply colimit.hom_ext
    intro i
    change colimit.ι (F ⋙ Over.forget _) i ≫ Closed.DiagramGluedStructure.equifiberedOverGluedMap q hq =
      colimit.ι (F ⋙ Over.forget _) i ≫
        (HasColimit.isoOfNatIso (Functor.isoWhiskerRight (asIso q) (Over.forget _))).hom
    rw [Cartesian.DiagramGluing.cartesianDiagramGluedMap_ι, HasColimit.ι_isoOfNatIso_hom]
    rfl
  rw [he]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EquifiberedGluedIsomorphism
