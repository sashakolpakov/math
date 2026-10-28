import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SectionGluing
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Section Sheaf -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SectionSheaf

noncomputable section

/-! The genuine module-valued sheaf of holomorphic vector-valued sections. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable (E F : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def holomorphicSectionPresheaf : TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of E) where
  obj U := ModuleCat.of ℂ (CoefficientMem.holomorphicSections U.unop F)
  map h := ModuleCat.ofHom (Restrictions.holomorphicSectionRestrict (leOfHom h.unop))
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rfl

theorem holomorphicSectionPresheaf_isSheaf : (holomorphicSectionPresheaf E F).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (holomorphicSectionPresheaf E F)).2
  intro ι U a ha
  have hc : ∀ i j (x : E) (hi : x ∈ U i) (hj : x ∈ U j),
      (a i).val ⟨x, hi⟩ = (a j).val ⟨x, hj⟩ := by
    intro i j x hi hj
    exact congrArg (fun b : CoefficientMem.holomorphicSections (U i ⊓ U j) F => b.val ⟨x, hi, hj⟩) (ha i j)
  obtain ⟨b, hb, hu⟩ := SectionGluing.existsUnique_holomorphicSection_glue U a hc
  refine ⟨b, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    funext x
    exact hb i x
  · intro c hc
    apply hu
    intro i x
    exact congrArg (fun d : CoefficientMem.holomorphicSections (U i) F => d.val x) (hc i)

def holomorphicSectionSheaf : TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of E) :=
  ⟨holomorphicSectionPresheaf E F, holomorphicSectionPresheaf_isSheaf E F⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SectionSheaf
