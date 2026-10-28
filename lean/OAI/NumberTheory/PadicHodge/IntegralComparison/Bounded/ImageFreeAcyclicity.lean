import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ImageResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Free.YonedaResolutionAcyclicity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SheafInjectives

/-! # Image Free Acyclicity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ImageFreeAcyclicity

noncomputable section

/-! Native bounded crystalline slice direct images are acyclic at
every actual bounded-site object, with free representable source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
open OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SliceImage

universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k))) [IsSeparated f] (n : ℕ)
  (U V : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

abbrev Cohomology (i : ℕ) := Abelian.Ext.{u + 2}
  (Sheaf.freeYoneda (BoundedCrystalline.Site.topology f n) V (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k))))
  ((SliceImage.directImage f n U).obj (BoundedCrystalline.SliceSheaves.structureSheaf f n U)) i

theorem positive_cohomology_zero (i : ℕ) : Subsingleton (Cohomology p k f n U V (i + 1)) := by
  let I := injectiveResolution (BigCrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) f)
  let ID := ImageResolution.resolution p k f n I U
  apply Free.YonedaResolutionAcyclicity.subsingleton.{u + 1,u,u + 2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (BoundedCrystalline.Site.topology f n) V ID i
  intro x hx
  exact Crystalline.ResolutionSections.sections_exact_succ p k f I
    (((Over.star U).obj V).left).obj i x hx

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ImageFreeAcyclicity
