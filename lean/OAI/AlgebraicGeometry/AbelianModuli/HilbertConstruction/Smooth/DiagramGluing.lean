import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Diagram Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.DiagramGluing

noncomputable section

/-! A finite locally directed diagram of smooth affine charts glues to a smooth noetherian scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v w

variable {C : Type u} [CommRing C] {J : Type v} [Category.{w} J] [Quiver.IsThin J] [Small.{u} J]
variable (F : J ⥤ Over (Spec (.of C)))
variable [∀ {i j} (h : i ⟶ j), IsOpenImmersion ((F ⋙ Over.forget (Spec (.of C))).map h)]
variable [((F ⋙ Over.forget (Spec (.of C))) ⋙ Scheme.forget).IsLocallyDirected]

def smoothDiagramGluedMap : colimit (F ⋙ Over.forget (Spec (.of C))) ⟶ Spec (.of C) :=
  colimit.desc (F ⋙ Over.forget (Spec (.of C))) {
    pt := Spec (.of C)
    ι := {
      app := fun i => (F.obj i).hom
      naturality := fun _ _ h => (F.map h).w.trans (Category.comp_id _).symm } }

theorem smoothDiagramGluedMap_ι (i : J) :
    colimit.ι (F ⋙ Over.forget (Spec (.of C))) i ≫ smoothDiagramGluedMap (C := C) F = (F.obj i).hom :=
  colimit.ι_desc _ _

instance smoothDiagramGluedMap_smooth [hs : ∀ i, Smooth (F.obj i).hom] :
    Smooth (smoothDiagramGluedMap (C := C) F) := by
  have : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := (@Smooth : MorphismProperty Scheme.{u}))
    (Scheme.IsLocallyDirected.openCover (F ⋙ Over.forget (Spec (.of C))))).mpr
  change ∀ i : J, Smooth (colimit.ι (F ⋙ Over.forget (Spec (.of C))) i ≫
    smoothDiagramGluedMap (C := C) F)
  intro i
  rw [smoothDiagramGluedMap_ι (C := C) F i]
  exact hs i

instance smoothDiagramGlued_compact [Finite J] [∀ i, IsAffine (F.obj i).left] :
    CompactSpace ↥(colimit (F ⋙ Over.forget (Spec (.of C))) : Scheme.{u}) := by
  let U := Scheme.IsLocallyDirected.openCover (F ⋙ Over.forget (Spec (.of C)))
  have : Finite U.I₀ := inferInstanceAs (Finite J)
  have hc : ∀ i : J, CompactSpace (F.obj i).left := fun i => Scheme.compactSpace_of_isAffine (F.obj i).left
  have : ∀ i : U.I₀, CompactSpace (U.X i) := hc
  exact U.compactSpace

theorem smoothDiagramGlued_noetherian [IsNoetherianRing C] [Finite J]
    [∀ i, IsAffine (F.obj i).left] [∀ i, Smooth (F.obj i).hom] :
    IsNoetherian (colimit (F ⋙ Over.forget (Spec (.of C)))) := by
  have : IsLocallyNoetherian (colimit (F ⋙ Over.forget (Spec (.of C)))) :=
    LocallyOfFiniteType.isLocallyNoetherian (smoothDiagramGluedMap (C := C) F)
  exact AlgebraicGeometry.IsNoetherian.mk

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.DiagramGluing
