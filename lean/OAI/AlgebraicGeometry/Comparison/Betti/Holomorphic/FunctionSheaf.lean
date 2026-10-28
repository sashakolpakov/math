import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SectionSheaf
import Mathlib.Algebra.Category.Ring.Limits

/-! # Function Sheaf -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionSheaf

noncomputable section

/-! The ring-valued sheaf of actual holomorphic functions, with actual open restrictions. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]

def holomorphicFunctionPresheaf : TopCat.Presheaf CommRingCat.{0} (TopCat.of E) where
  obj U := CommRingCat.of (FunctionPure.holomorphicFunctions U.unop)
  map h := CommRingCat.ofHom (Restrictions.holomorphicFunctionRestrict (leOfHom h.unop)).toRingHom
  map_id U := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    rfl
  map_comp f g := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    rfl

theorem holomorphicFunctionPresheaf_isSheaf : (holomorphicFunctionPresheaf E).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (holomorphicFunctionPresheaf E)).2
  intro ι U a ha
  have hs := (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing
    (SectionSheaf.holomorphicSectionPresheaf E ℂ)).mp (SectionSheaf.holomorphicSectionPresheaf_isSheaf E ℂ)
  exact hs U a ha

def holomorphicFunctionSheaf : TopCat.Sheaf CommRingCat.{0} (TopCat.of E) :=
  ⟨holomorphicFunctionPresheaf E, holomorphicFunctionPresheaf_isSheaf E⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionSheaf
