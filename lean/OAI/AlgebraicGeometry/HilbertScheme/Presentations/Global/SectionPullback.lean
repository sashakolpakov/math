import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.SectionLinearCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SectionPullbackEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarBaseChange

/-! # Section Pullback -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.SectionPullback

noncomputable section

/-! Pullback of literal global module sections is additive and
semilinear for the actual map on global regular functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarBaseChange

universe u
variable {X Y : Scheme.{u}}

def moduleGlobalSectionPullback (f : X ⟶ Y) (M : Y.Modules) :
    Γ(M, ⊤) → Γ((Scheme.Modules.pullback f).obj M, ⊤) :=
  fun s => AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv _ (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).symm s))

theorem moduleGlobalSectionPullback_add (f : X ⟶ Y) (M : Y.Modules) (s t : Γ(M, ⊤)) :
    moduleGlobalSectionPullback f M (s + t) = moduleGlobalSectionPullback f M s + moduleGlobalSectionPullback f M t := by
  unfold moduleGlobalSectionPullback
  rw [SectionLinearCoordinates.moduleSectionHomEquiv_symm_add]
  simp only [AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection, Functor.map_add, Preadditive.comp_add, SectionLinearCoordinates.moduleSectionHomEquiv_add]

theorem moduleGlobalSectionPullback_smul (f : X ⟶ Y) (M : Y.Modules) (r : Γ(Y, ⊤)) (s : Γ(M, ⊤)) :
    moduleGlobalSectionPullback f M (r • s) = f.appTop r • moduleGlobalSectionPullback f M s := by
  unfold moduleGlobalSectionPullback
  rw [SectionLinearCoordinates.moduleSectionHomEquiv_symm_smul]
  simp only [AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection, Functor.map_comp, AbelianModuli.HilbertConstruction.Global.ScalarBaseChange.globalModuleScalar_pullback]
  rw [← Category.assoc, SectionLinearCoordinates.moduleSectionHomEquiv_scalar]

theorem moduleGlobalSectionPullback_bijective (e : X ≅ Y) (M : Y.Modules) :
    Function.Bijective (moduleGlobalSectionPullback e.hom M) :=
  (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback e.hom).obj M)).bijective.comp
    ((SectionPullbackEquivalence.sectionPullback_bijective e M).comp (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M).symm.bijective)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.SectionPullback
