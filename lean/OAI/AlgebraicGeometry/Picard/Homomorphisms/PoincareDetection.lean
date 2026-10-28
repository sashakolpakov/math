import OAI.AlgebraicGeometry.Picard.Homomorphisms.SheafMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data

/-! # Poincare Detection -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.PoincareDetection

noncomputable section

/-!
# Homomorphisms: Poincare classes detect morphisms to the actual dual

This uses the existing representation of the homogeneous Picard sheaf and
the proved inclusion of that sheaf into the relative Picard sheaf.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

instance homogeneousPicardInclusion_mono : Mono A.homogeneousPicardInclusion := by
  have (T : (Over S)ᵒᵖ) : Mono (A.homogeneousPicardInclusion.app T) :=
    (CategoryTheory.mono_iff_injective _).mpr Subtype.val_injective
  exact NatTrans.mono_of_mono_app _

instance homogeneousPicardSheafInclusion_mono : Mono A.homogeneousPicardSheafInclusion :=
  inferInstanceAs (Mono ((presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
    A.homogeneousPicardInclusion))

theorem homogeneousPicardSheafInclusion_toSheafify :
    toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf ≫
        A.homogeneousPicardSheafInclusion.hom =
      A.homogeneousPicardInclusion ≫ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme :=
  (toSheafify_naturality _ _).symm

variable {A}

def poincareClass (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {T : Over S} (f : T ⟶ D.abelian.scheme) :
    AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections A.scheme T :=
  (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (f ▷ A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))

theorem poincareClass_id (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) :
    poincareClass D (𝟙 D.abelian.scheme) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op D.abelian.scheme) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare) := by
  dsimp only [poincareClass]
  erw [id_whiskerRight, Over.id_left, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id]
  rfl

theorem poincareClass_eq_representation (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {T : Over S}
    (f : T ⟶ D.abelian.scheme) :
    poincareClass D f = A.homogeneousPicardSheafInclusion.hom.app (.op T)
      (D.representable.homEquiv f) := by
  have h := D.representable.homEquiv_comp f (𝟙 D.abelian.scheme)
  rw [Category.comp_id, D.universalClass] at h
  rw [h]
  have hn := (toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).naturality_apply
    f.op ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare, D.poincareHomogeneous⟩
  erw [← hn]
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app
    (homogeneousPicardSheafInclusion_toSheafify A) (.op T))
      (A.homogeneousPicardPresheaf.map f.op
        ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare, D.poincareHomogeneous⟩)).symm

theorem poincareClass_injective (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (T : Over S) :
    Function.Injective (poincareClass D (T := T)) := by
  intro f h e
  rw [poincareClass_eq_representation, poincareClass_eq_representation] at e
  have hi : Mono (A.homogeneousPicardSheafInclusion.hom.app (.op T)) := inferInstance
  apply D.representable.homEquiv.injective
  exact (CategoryTheory.mono_iff_injective _).mp hi e

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.PoincareDetection
