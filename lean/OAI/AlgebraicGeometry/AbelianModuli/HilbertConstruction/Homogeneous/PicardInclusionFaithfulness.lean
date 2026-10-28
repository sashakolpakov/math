import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.PicardSections
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # Picard Inclusion Faithfulness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Homogeneous Picard sections embed into relative Picard sections after sheafification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Abelian.Schemes.AbelianScheme.homogeneousPicardSectionInclusion_injective
    {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (T : Over S) :
    Function.Injective (A.homogeneousPicardSectionInclusion T) := by
  have hm : Mono A.homogeneousPicardInclusion := by
    apply (NatTrans.mono_iff_mono_app _).mpr
    intro U
    exact (CategoryTheory.mono_iff_injective _).mpr Subtype.val_injective
  have hs : Mono A.homogeneousPicardSheafInclusion :=
    (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map_mono A.homogeneousPicardInclusion
  have hp : Mono A.homogeneousPicardSheafInclusion.hom :=
    (sheafToPresheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map_mono A.homogeneousPicardSheafInclusion
  exact CategoryTheory.injective_of_mono (A.homogeneousPicardSheafInclusion.hom.app (.op T))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
