import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SliceImage
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ResolutionSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafExactSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.LeftExactResolution

/-! # Image Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ImageResolution

noncomputable section

/-!
# IntegralComparison: actual direct-image injective resolutions at bounded Witt levels
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
open OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SliceImage

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k))) [IsSeparated f] (n : ℕ)
  (I : InjectiveResolution (BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f))
  (U : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

abbrev functor : Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f ⥤
    BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n :=
  BoundedCrystalline.Site.restriction f n ⋙ SliceImage.restriction f n U ⋙ SliceImage.directImage f n U

def complex : CochainComplex (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n) ℕ :=
  LeftExactResolution.complex (functor p k f n U) I

theorem positive_exact (i : ℕ) : (complex p k f n I U).ExactAt (i + 1) := by
  apply (HomologicalComplex.exactAt_iff' _ i (i + 1) (i + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)).mpr
  apply Module.SheafExactSections.exact_of_sections (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (BoundedCrystalline.Site.topology f n)
  intro V x hx
  exact Crystalline.ResolutionSections.sections_exact_succ p k f I
    (((Over.star U).obj V).left).obj i x hx

def resolution : InjectiveResolution
    ((SliceImage.directImage f n U).obj (BoundedCrystalline.SliceSheaves.structureSheaf f n U)) :=
  LeftExactResolution.resolution (functor p k f n U) I (positive_exact p k f n I U)

def sliceResolution : InjectiveResolution (BoundedCrystalline.SliceSheaves.structureSheaf f n U) :=
  ExactInjectiveResolution.map
    (BoundedCrystalline.Site.restriction f n ⋙ SliceImage.restriction f n U) I

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ImageResolution
