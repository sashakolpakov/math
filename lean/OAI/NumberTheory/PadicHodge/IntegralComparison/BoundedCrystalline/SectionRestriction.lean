import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineSections
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ConstantRestrictionCoherence

/-! # Section Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.SectionRestriction

noncomputable section

/-! The actual bounded crystalline Ext restriction in degree zero restricts the original presheaf section. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry Opposite

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)

def boundedHomEquiv :
    (CrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) f n ⟶
      CrystallineCohomology.structureSheaf f n) ≃ₗ[R]
        CrystallineSections.Sections (p := p) (J := J) (δ := δ) f n :=
  (LinearAdjunction.homLinearEquiv R
    (sheafificationAdjunction (Site.topology f n) (ModuleCat.{u + 1} R))
    ((Functor.const (Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ).obj
      (ModuleCat.of R R)) (CrystallineCohomology.structureSheaf f n)).trans
    (Linear.homCongr R (Iso.refl _) (Bounded.CohomologyTorsion.structurePresheafIso f n).symm)

theorem hom (a : BigCrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) f ⟶ BigCrystallineCohomology.structureSheaf f) :
    boundedHomEquiv f n ((CrystallineCohomology.constantUnitIso f n).inv ≫
      (Site.restriction f n).map a) =
        CrystallineSections.restriction f n
          (Sheafified.PresheafSections.homLinearEquiv R BigCrystallineSite.Object.topology (BigCrystallineCohomology.largePresheaf f)
            (Crystalline.StructureDescent.largePresheaf_isSheaf f) (ModuleCat.of R R) a) := by
  have h := PeriodInvariants.ConstantRestrictionCoherence.transport_generator
    (Site.topology f n) BigCrystallineSite.Object.topology
      (Site.inclusion (p := p) (J := J) (δ := δ) f n) (ModuleCat.of R R)
  change (toSheafify (Site.topology f n)
      ((Functor.const _).obj (ModuleCat.of R R))) ≫
        (CrystallineCohomology.constantUnitIso f n).inv.hom =
    Functor.whiskerLeft (Site.inclusion f n).op
      (toSheafify BigCrystallineSite.Object.topology ((Functor.const _).obj (ModuleCat.of R R))) at h
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hv := congrArg (fun t => t.app U x) h
  change (Crystalline.StructureDescent.structurePresheafIso f).inv.app (op U.unop.obj)
      (a.hom.app (op U.unop.obj)
        ((CrystallineCohomology.constantUnitIso f n).inv.hom.app U
          ((toSheafify (Site.topology f n)
            ((Functor.const _).obj (ModuleCat.of R R))).app U x))) =
    (Crystalline.StructureDescent.structurePresheafIso f).inv.app (op U.unop.obj)
      (a.hom.app (op U.unop.obj)
        ((toSheafify BigCrystallineSite.Object.topology ((Functor.const _).obj (ModuleCat.of R R))).app
          (op U.unop.obj) x))
  exact congrArg (fun y => (Crystalline.StructureDescent.structurePresheafIso f).inv.app
    (op U.unop.obj) (a.hom.app (op U.unop.obj) y)) hv

theorem cohomology (x : BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f 0) :
    CrystallineSections.cohomologyEquiv f n
        (CrystallineCohomology.restriction f n 0 x) =
      CrystallineSections.restriction f n (Crystalline.ConstantSections.cohomologyEquiv f x) := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
  change CrystallineSections.cohomologyEquiv f n
    (((Ext.mk₀ _).comp ((Ext.mk₀ a).mapExactFunctor _) (Nat.zero_add 0)).comp
      (Ext.mk₀ (𝟙 _)) (Nat.add_zero 0)) = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, Category.comp_id]
  change boundedHomEquiv f n (Ext.linearEquiv₀ (Ext.mk₀ _)) =
    CrystallineSections.restriction f n
      (Sheafified.PresheafSections.homLinearEquiv R BigCrystallineSite.Object.topology (BigCrystallineCohomology.largePresheaf f)
        (Crystalline.StructureDescent.largePresheaf_isSheaf f) (ModuleCat.of R R)
        (Ext.linearEquiv₀ (Ext.mk₀ a)))
  exact (congrArg (boundedHomEquiv f n)
    ((Ext.linearEquiv₀ («R» := R)).apply_symm_apply
      ((CrystallineCohomology.constantUnitIso f n).inv ≫
        (Site.restriction f n).map a))).trans
    ((SectionRestriction.hom f n a).trans (congrArg (fun b => CrystallineSections.restriction f n
      (Sheafified.PresheafSections.homLinearEquiv R BigCrystallineSite.Object.topology (BigCrystallineCohomology.largePresheaf f)
        (Crystalline.StructureDescent.largePresheaf_isSheaf f) (ModuleCat.of R R) b))
          ((Ext.linearEquiv₀ («R» := R)).apply_symm_apply a).symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.SectionRestriction
