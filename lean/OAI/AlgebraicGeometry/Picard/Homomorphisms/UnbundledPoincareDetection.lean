import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData
import OAI.AlgebraicGeometry.Picard.Homomorphisms.SheafMaps

/-! # Unbundled Poincare Detection -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPoincareDetection

noncomputable section

/-! Dimension-independent poincare detection,
using the actual line bundles and represented homogeneous Picard sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction.UnbundledPicard

universe u
variable {S : Scheme.{u}} (A : Over S) [GrpObj A]

instance homogeneousPicardInclusion_mono : Mono (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardInclusion A) := by
  have (T : (Over S)ᵒᵖ) : Mono ((UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardInclusion A).app T) :=
    (CategoryTheory.mono_iff_injective _).mpr Subtype.val_injective
  exact NatTrans.mono_of_mono_app _

instance homogeneousPicardSheafInclusion_mono : Mono (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion A) :=
  inferInstanceAs (Mono ((presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
    (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardInclusion A)))

theorem homogeneousPicardSheafInclusion_toSheafify :
    toSheafify (Scheme.fppfTopology.over S) (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A) ≫
        (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion A).hom =
      (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardInclusion A) ≫ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A :=
  (toSheafify_naturality _ _).symm

variable {A}

def poincareClass (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) {T : Over S} (f : T ⟶ D.abelian) :
    AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections A T :=
  (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (f ▷ A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))

theorem poincareClass_id (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) :
    poincareClass D (𝟙 D.abelian) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op D.abelian) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare) := by
  dsimp only [poincareClass]
  erw [id_whiskerRight, Over.id_left, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id]
  rfl

theorem poincareClass_eq_representation (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) {T : Over S}
    (f : T ⟶ D.abelian) :
    poincareClass D f = (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion A).hom.app (.op T)
      (D.representable.homEquiv f) := by
  have h := D.representable.homEquiv_comp f (𝟙 D.abelian)
  rw [Category.comp_id, D.universalClass] at h
  rw [h]
  have hn := (toSheafify (Scheme.fppfTopology.over S) (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)).naturality_apply
    f.op ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare, D.poincareHomogeneous⟩
  erw [← hn]
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app
    (homogeneousPicardSheafInclusion_toSheafify A) (.op T))
      ((UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A).map f.op
        ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare, D.poincareHomogeneous⟩)).symm

theorem poincareClass_injective (D : UnbundledDualData.Construction.UnbundledPicard.DualData A) (T : Over S) :
    Function.Injective (poincareClass D (T := T)) := by
  intro f h e
  rw [poincareClass_eq_representation, poincareClass_eq_representation] at e
  have hi : Mono ((UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion A).hom.app (.op T)) := inferInstance
  apply D.representable.homEquiv.injective
  exact (CategoryTheory.mono_iff_injective _).mp hi e

end Construction.UnbundledPicard

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPoincareDetection
