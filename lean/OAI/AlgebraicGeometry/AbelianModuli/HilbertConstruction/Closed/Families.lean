import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Families -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.Families

noncomputable section

/-!
Flat finitely presented closed families in a fixed ambient scheme, recorded
by their actual ideal sheaves. These are parameter objects for the later
embedded-family construction; no representing scheme is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}}

/-- A closed subscheme of an ambient `S`-scheme, flat and locally finitely presented over `S`. -/
structure FlatClosedFamily (P : Over S) where
  ideal : P.left.IdealSheafData
  flat : Flat (ideal.subschemeι ≫ P.hom)
  locallyFinitePresentation : LocallyOfFinitePresentation (ideal.subschemeι ≫ P.hom)

attribute [instance] FlatClosedFamily.flat FlatClosedFamily.locallyFinitePresentation

namespace FlatClosedFamily

variable {P : Over S}

/-- The family scheme cut out by the ideal. -/
def scheme (F : FlatClosedFamily P) : Over S := Over.mk (F.ideal.subschemeι ≫ P.hom)

/-- Its closed inclusion in the ambient scheme. -/
def inclusion (F : FlatClosedFamily P) : F.scheme ⟶ P := Over.homMk F.ideal.subschemeι rfl

instance inclusion_closedImmersion (F : FlatClosedFamily P) : IsClosedImmersion F.inclusion.left :=
  inferInstanceAs (IsClosedImmersion F.ideal.subschemeι)

theorem proper (F : FlatClosedFamily P) [IsProper P.hom] : IsProper F.scheme.hom :=
  inferInstanceAs (IsProper (F.ideal.subschemeι ≫ P.hom))

/-- An embedded flat finitely presented scheme determines its ideal-sheaf family. -/
def ofEmbedding {Z : Over S} (i : Z ⟶ P) [IsClosedImmersion i.left]
    [Flat Z.hom] [LocallyOfFinitePresentation Z.hom] : FlatClosedFamily P := by
  let e := asIso i.left.toImage
  have he : e.hom ≫ (i.left.ker.subschemeι ≫ P.hom) = Z.hom :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ P.hom) i.left.toImage_imageι).trans i.w)
  have hq : i.left.ker.subschemeι ≫ P.hom = e.inv ≫ Z.hom := by
    rw [← he]
    simp only [Iso.inv_hom_id_assoc]
  exact ⟨i.left.ker, hq.symm ▸ (inferInstance : Flat (e.inv ≫ Z.hom)),
    hq.symm ▸ (inferInstance : LocallyOfFinitePresentation (e.inv ≫ Z.hom))⟩

/-- The ideal-sheaf family recovers the original embedded scheme over the base. -/
def ofEmbeddingIso {Z : Over S} (i : Z ⟶ P) [IsClosedImmersion i.left]
    [Flat Z.hom] [LocallyOfFinitePresentation Z.hom] :
    Z ≅ (ofEmbedding i).scheme := by
  let e : Z.left ≅ i.left.ker.subscheme := asIso i.left.toImage
  exact Over.isoMk e
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ P.hom) i.left.toImage_imageι).trans i.w))

end FlatClosedFamily

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.Families
