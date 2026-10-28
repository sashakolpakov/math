import OAI.NumberTheory.PadicHodge.IntegralComparison.Free.YonedaAcyclicity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SliceImage
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SliceCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SheafInjectives

/-! # Free Yoneda Acyclicity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.FreeYonedaAcyclicity

noncomputable section

/-! Every actual bounded crystalline frame gives a source acyclic for the original structure sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k))) (n : ℕ)
  (U : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

abbrev source : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n :=
  Sheaf.freeYoneda (BoundedCrystalline.Site.topology f n) U
    (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (Crystalline.ExactRestriction.Coeff (B := WittVector p k)))

theorem subsingleton (i : ℕ) :
    Subsingleton (Abelian.Ext.{u + 2} (source p k f n U)
      (BoundedCrystalline.CrystallineCohomology.structureSheaf f n) (i + 1)) := by
  let I := injectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) f n)
  let : Subsingleton (SliceCohomology.Cohomology f n U (i + 1)) :=
    SliceCohomology.positive_cohomology_zero p k f n U i
  exact Free.YonedaAcyclicity.subsingleton (BoundedCrystalline.Site.topology f n) U
    (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) I i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.FreeYonedaAcyclicity
