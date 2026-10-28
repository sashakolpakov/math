import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.ResolutionTerms
import OAI.NumberTheory.PadicHodge.IntegralComparison.Free.PresentationAcyclicity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.FreeYonedaAcyclicity

/-! # Resolution Acyclicity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.ResolutionAcyclicity

noncomputable section

/-! The actual global frame resolution is source-acyclic for the original crystalline structure sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k))) [IsSeparated f] (n : ℕ)
  {ι : Type u} (F : ι → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

theorem subsingleton (a i : ℕ) :
    Subsingleton (Abelian.Ext.{u + 2}
      ((CoveringPresentationResolution.complex.{u + 1, u} (BoundedCrystalline.Site.topology f n) R F).X a)
      (BoundedCrystalline.CrystallineCohomology.structureSheaf f n) (i + 1)) := by
  let I := injectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) f n)
  let P := Presentation.TupleProducts.family.{u + 1, u} F a
  let hP : ∀ t, Subsingleton (Abelian.Ext.{u + 2}
      (Sheaf.freeYoneda (BoundedCrystalline.Site.topology f n) (P t) (ModuleCat.of R R))
      (BoundedCrystalline.CrystallineCohomology.structureSheaf f n) (i + 1)) :=
    fun t => Bounded.FreeYonedaAcyclicity.subsingleton p k f n (P t) i
  let : Subsingleton (Abelian.Ext.{u + 2}
      (Free.PresentationSheafSections.sheaf.{u + 1, u} P R (BoundedCrystalline.Site.topology f n))
      (BoundedCrystalline.CrystallineCohomology.structureSheaf f n) (i + 1)) :=
    Free.PresentationAcyclicity.subsingleton.{u + 1, u, u + 2} P R (BoundedCrystalline.Site.topology f n) I i
  exact (Etale.Frobenius.extIsoCongr R
    (Presentation.ResolutionTerms.sheafIso.{u + 1, u} F R a (BoundedCrystalline.Site.topology f n))
      (Iso.refl (BoundedCrystalline.CrystallineCohomology.structureSheaf f n)) (i + 1)).toEquiv.subsingleton

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.ResolutionAcyclicity
