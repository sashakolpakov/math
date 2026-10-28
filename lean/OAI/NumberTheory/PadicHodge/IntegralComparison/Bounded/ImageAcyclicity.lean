import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ImageResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SliceSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.Acyclicity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SheafInjectives

/-! # Image Acyclicity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ImageAcyclicity

noncomputable section

/-!
# IntegralComparison: actual bounded-level direct images are acyclic
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
open OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SliceImage

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k))) [IsSeparated f] (n : ℕ)
  (U : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

abbrev Cohomology (i : ℕ) := Abelian.Ext.{u + 2}
  (BoundedCrystalline.CrystallineCohomology.constantUnit f n)
  ((SliceImage.directImage f n U).obj (BoundedCrystalline.SliceSheaves.structureSheaf f n U)) i

theorem positive_cohomology_zero (i : ℕ) : Subsingleton (Cohomology p k f n U (i + 1)) := by
  let I := injectiveResolution (BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f)
  let IU := ImageResolution.sliceResolution p k f n I U
  let ID := ImageResolution.resolution p k f n I U
  have := SliceCohomology.positive_cohomology_zero p k f n U i
  exact ResolutionHom.Acyclicity.subsingleton ID IU
    (fun m => SliceSections.homEquiv f n U (IU.cocomplex.X m))
    (fun m a => SliceSections.homEquiv_natural f n U a (IU.cocomplex.d m (m + 1))) i

def degreeZeroEquiv : Cohomology p k f n U 0 ≃+ ULift.{u + 1} U.obj.ring :=
  (SliceSections.degreeZeroEquiv f n U (BoundedCrystalline.SliceSheaves.structureSheaf f n U)).trans
    (SliceCohomology.degreeZeroEquiv p k f n U)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ImageAcyclicity
