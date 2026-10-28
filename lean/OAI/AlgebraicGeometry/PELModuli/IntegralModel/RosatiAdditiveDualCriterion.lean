import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualFamilyMorphism
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.Actions

/-! # Rosati Additive Dual Criterion -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiAdditiveDualCriterion

noncomputable section

/-! A finite integral basis detects Rosati compatibility whenever the
actual additive dual morphisms and their Poincare identities are given.
This criterion applies on arbitrary test schemes. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem rosati_iff_basis_equations_of_dual_addHom
    {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Scheme} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (d : NumberField.RingOfIntegers E →+ Finite.Actions.GroupEndRing A.dual.abelian)
    (hp : ∀ a, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((d a).hom A.dual.abelian ⊗ₘ 𝟙 A.abelian.scheme).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 A.dual.abelian.scheme ⊗ₘ ρ.map a).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare)) :
    AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ ↔
      ∀ i : Fin (Module.finrank ℤ (NumberField.RingOfIntegers E)),
        A.polarization.isogeny.hom ≫ (d (Finite.Actions.integralActionBasis E i)).hom A.dual.abelian =
          ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E (Finite.Actions.integralActionBasis E i)) ≫
            A.polarization.isogeny.hom := by
  constructor
  · intro h i
    obtain ⟨q, _, hq, he⟩ := h (Finite.Actions.integralActionBasis E i)
    have hd := DualFamilyMorphism.eq_dualPicardPullback_of_poincare A.dual A.dual
      (ρ.map (Finite.Actions.integralActionBasis E i)) _ (hp (Finite.Actions.integralActionBasis E i))
    have hq' := DualFamilyMorphism.eq_dualPicardPullback_of_poincare A.dual A.dual
      (ρ.map (Finite.Actions.integralActionBasis E i)) q hq
    rw [hd.trans hq'.symm]
    exact he
  · intro hb
    let ell := A.polarization.isogeny.hom
    let r := (Finite.Actions.ringHomOfIntegralAction A.abelian ρ).toAddMonoidHom.comp
      (NumberField.IsCMField.ringOfIntegersComplexConj E).toAddMonoidHom
    let L : NumberField.RingOfIntegers E →+
        Additive (A.abelian.scheme ⟶ A.dual.abelian.scheme) :=
      { toFun := fun a => Additive.ofMul (ell ≫ (d a).hom A.dual.abelian)
        map_zero' := by
          change Additive.ofMul (ell ≫ (d 0).hom _) = Additive.ofMul 1
          rw [map_zero, Finite.Actions.GroupEndRing.hom_zero]
          exact congrArg Additive.ofMul (MonObj.comp_one ell)
        map_add' a b := by
          change Additive.ofMul (ell ≫ (d (a + b)).hom _) =
            Additive.ofMul ((ell ≫ (d a).hom _) * (ell ≫ (d b).hom _))
          rw [map_add, Finite.Actions.GroupEndRing.hom_add]
          exact congrArg Additive.ofMul (MonObj.comp_mul ell _ _) }
    let R : NumberField.RingOfIntegers E →+
        Additive (A.abelian.scheme ⟶ A.dual.abelian.scheme) :=
      { toFun := fun a => Additive.ofMul ((r a).hom A.abelian ≫ ell)
        map_zero' := by
          change Additive.ofMul ((r 0).hom _ ≫ ell) = Additive.ofMul 1
          rw [map_zero, Finite.Actions.GroupEndRing.hom_zero]
          exact congrArg Additive.ofMul (MonObj.one_comp ell)
        map_add' a b := by
          change Additive.ofMul ((r (a + b)).hom _ ≫ ell) =
            Additive.ofMul (((r a).hom _ ≫ ell) * ((r b).hom _ ≫ ell))
          rw [map_add, Finite.Actions.GroupEndRing.hom_add]
          exact congrArg Additive.ofMul (MonObj.mul_comp _ _ ell) }
    have heq : L.toIntLinearMap = R.toIntLinearMap :=
      (Finite.Actions.integralActionBasis E).ext fun i => congrArg Additive.ofMul (hb i)
    intro a
    refine ⟨(d a).hom A.dual.abelian, inferInstance, hp a, ?_⟩
    exact congrArg Additive.toMul (LinearMap.congr_fun heq a)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiAdditiveDualCriterion
