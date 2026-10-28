import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiAdditiveDualCriterion
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.DualEndomorphismAdditivity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RosatiBaseChange

/-! # Rosati Basis Pullback -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.RosatiBasisPullback

noncomputable section

/-! Finite actual Rosati equations on any reduced noetherian abelian
parameter family characterize Rosati compatibility after arbitrary base
change. No finiteness or reducedness is required of the test scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem rosati_iff_relative_pulledBack_basis_equations
    {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Scheme.{0}} [IsReduced S] [IsNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {T : Scheme.{0}} (f : T ⟶ S) :
    AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback f) (ρ.pullback f) ↔
      ∀ i : Fin (Module.finrank ℤ (NumberField.RingOfIntegers E)),
        (Over.pullback f).map (A.polarization.isogeny.hom ≫
          Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback A.dual A.dual
            (ρ.map (Finite.Actions.integralActionBasis E i))) =
        (Over.pullback f).map
          (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E (Finite.Actions.integralActionBasis E i)) ≫
            A.polarization.isogeny.hom) := by
  let d₀ := (DualEndomorphismAdditivity.relativeDualGroupEndAddHom A.dual).comp
    (Finite.Actions.ringHomOfIntegralAction A.abelian ρ).toAddMonoidHom
  let d := (Finite.Actions.GroupEndRing.pullback A.dual.abelian f).toAddMonoidHom.comp d₀
  have hp (b : NumberField.RingOfIntegers E) :
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
        ((d b).hom (A.pullback f).dual.abelian ⊗ₘ
          𝟙 (A.pullback f).abelian.scheme).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (A.pullback f).dual.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
        (𝟙 (A.pullback f).dual.abelian.scheme ⊗ₘ (ρ.pullback f).map b).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (A.pullback f).dual.poincare) := by
    have h₀ := DualEndomorphismAdditivity.relativeDualGroupEnd_leftClass A.dual
      (Finite.Actions.ringHomOfIntegralAction A.abelian ρ b)
    have h₁ := AbelianModuli.ReferenceFamily.RosatiBaseChange.poincareEndomorphism_baseChange A.dual
      ((d₀ b).hom A.dual.abelian) (𝟙 A.abelian.scheme) f
    have h₂ := AbelianModuli.ReferenceFamily.RosatiBaseChange.poincareEndomorphism_baseChange A.dual
      (𝟙 A.dual.abelian.scheme) (ρ.map b) f
    rw [(Over.pullback f).map_id] at h₁ h₂
    exact h₁.trans ((congrArg
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.dual.poincarePullbackOverMap f).left) h₀).trans h₂.symm)
  rw [RosatiAdditiveDualCriterion.rosati_iff_basis_equations_of_dual_addHom (A.pullback f) (ρ.pullback f) d hp]
  apply forall_congr'
  intro i
  rw [(Over.pullback f).map_comp, (Over.pullback f).map_comp]
  rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.RosatiBasisPullback
