import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EquifiberedOverDiagrams
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.DiagramOpenIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.DiagramGluing

/-! # Diagram Glued Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramGluedIsomorphisms

noncomputable section

/-! Isomorphic affine chart diagrams glue to isomorphic schemes over their base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

variable {C : Type u} [CommRing C] {J : Type v} [Category J] [Quiver.IsThin J] [Small.{u} J]
variable {F G : J ⥤ Over (Spec (.of C))} (e : F ≅ G)
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (G.map h).left]
variable [((G ⋙ Over.forget (Spec (.of C))) ⋙ Scheme.forget).IsLocallyDirected]
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion (F.map h).left]
variable [((F ⋙ Over.forget (Spec (.of C))) ⋙ Scheme.forget).IsLocallyDirected]

local instance {i j : J} (h : i ⟶ j) : IsOpenImmersion ((G ⋙ Over.forget (Spec (.of C))).map h) :=
  inferInstanceAs (IsOpenImmersion (G.map h).left)

local instance {i j : J} (h : i ⟶ j) : IsOpenImmersion ((F ⋙ Over.forget (Spec (.of C))).map h) :=
  inferInstanceAs (IsOpenImmersion (F.map h).left)

def diagramGluedOverIso : Over.mk (Smooth.DiagramGluing.smoothDiagramGluedMap F) ≅ Over.mk (Smooth.DiagramGluing.smoothDiagramGluedMap G) := by
  let w := Functor.isoWhiskerRight e (Over.forget (Spec (.of C)))
  let z := HasColimit.isoOfNatIso w
  refine Over.isoMk z ?_
  apply colimit.hom_ext
  intro i
  change colimit.ι (F ⋙ Over.forget _) i ≫ (z.hom ≫ Smooth.DiagramGluing.smoothDiagramGluedMap G) =
    colimit.ι (F ⋙ Over.forget _) i ≫ Smooth.DiagramGluing.smoothDiagramGluedMap F
  rw [← Category.assoc, HasColimit.ι_isoOfNatIso_hom, Category.assoc,
    Smooth.DiagramGluing.smoothDiagramGluedMap_ι, Smooth.DiagramGluing.smoothDiagramGluedMap_ι]
  exact (e.hom.app i).w

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramGluedIsomorphisms
