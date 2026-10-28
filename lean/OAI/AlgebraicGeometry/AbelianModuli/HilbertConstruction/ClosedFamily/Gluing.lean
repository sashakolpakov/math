import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdealGluing

/-! # Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Effective gluing retains flatness and local finite presentation of embedded families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y S : Scheme.{u}} {C : X.OpenCover} [Category C.I₀] [C.LocallyDirected]
variable [Small.{u} C.I₀] [Quiver.IsThin C.I₀]

/-- Any property local on the source passes from the local closed families to the glued family. -/
theorem IdealDescent.IdealDescentData.glued_property (D : IdealDescent.IdealDescentData C) (p : X ⟶ Y)
    (W : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource W]
    (h : ∀ i, W ((D.ideal i).subschemeι ≫ C.f i ≫ p)) :
    W (D.relativeGluingData.toBase ≫ p) := by
  apply IsZariskiLocalAtSource.of_openCover (P := W) D.relativeGluingData.cover
  intro i
  have hi : D.relativeGluingData.cover.f i ≫ D.relativeGluingData.toBase =
      (D.ideal i).subschemeι ≫ C.f i := D.relativeGluingData.ι_toBase i
  have he : D.relativeGluingData.cover.f i ≫ (D.relativeGluingData.toBase ≫ p) =
      (D.ideal i).subschemeι ≫ C.f i ≫ p :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ p) hi).trans (Category.assoc _ _ _))
  exact (congrArg (fun f : (D.ideal i).subscheme ⟶ Y => W f) he).mpr (h i)

variable {P : Over S} {C : P.left.OpenCover} [Category C.I₀] [C.LocallyDirected]
variable [Small.{u} C.I₀] [Quiver.IsThin C.I₀]

/-- Glue compatible ideals whose local closed families are flat and locally finitely presented. -/
def Closed.Families.FlatClosedFamily.glue (D : IdealDescent.IdealDescentData C)
    (hflat : ∀ i, Flat ((D.ideal i).subschemeι ≫ C.f i ≫ P.hom))
    (hfinite : ∀ i, LocallyOfFinitePresentation ((D.ideal i).subschemeι ≫ C.f i ≫ P.hom)) :
    Closed.Families.FlatClosedFamily P := by
  let Z : Over S := Over.mk (D.relativeGluingData.toBase ≫ P.hom)
  let i : Z ⟶ P := Over.homMk D.relativeGluingData.toBase rfl
  letI : IsZariskiLocalAtSource (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  letI : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  have : Flat Z.hom := D.glued_property P.hom (@Flat.{u}) hflat
  have : LocallyOfFinitePresentation Z.hom :=
    D.glued_property P.hom (@LocallyOfFinitePresentation.{u}) hfinite
  have : IsClosedImmersion i.left := D.glued_closedImmersion
  exact Closed.Families.FlatClosedFamily.ofEmbedding i

/-- The glued family's defining ideal has the prescribed local restrictions. -/
theorem Closed.Families.FlatClosedFamily.glue_ideal_comap (D : IdealDescent.IdealDescentData C)
    (hflat : ∀ i, Flat ((D.ideal i).subschemeι ≫ C.f i ≫ P.hom))
    (hfinite : ∀ i, LocallyOfFinitePresentation ((D.ideal i).subschemeι ≫ C.f i ≫ P.hom))
    (i : C.I₀) : (Closed.Families.FlatClosedFamily.glue D hflat hfinite).ideal.comap (C.f i) = D.ideal i :=
  D.gluedIdeal_comap i

/-- Compatible local ideal families with the required geometric properties glue uniquely. -/
theorem Closed.Families.FlatClosedFamily.existsUnique_glued_family (D : IdealDescent.IdealDescentData C)
    (hflat : ∀ i, Flat ((D.ideal i).subschemeι ≫ C.f i ≫ P.hom))
    (hfinite : ∀ i, LocallyOfFinitePresentation ((D.ideal i).subschemeι ≫ C.f i ≫ P.hom)) :
    ∃! F : Closed.Families.FlatClosedFamily P, ∀ i, F.ideal.comap (C.f i) = D.ideal i := by
  refine ⟨Closed.Families.FlatClosedFamily.glue D hflat hfinite, Closed.Families.FlatClosedFamily.glue_ideal_comap D hflat hfinite, ?_⟩
  intro F hF
  exact F.ext_on_open_cover _ C
    (fun i => (hF i).trans (Closed.Families.FlatClosedFamily.glue_ideal_comap D hflat hfinite i).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
