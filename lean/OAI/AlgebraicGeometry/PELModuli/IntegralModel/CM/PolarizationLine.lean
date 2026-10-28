import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.ActionGeneratorFaithfulness
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PoincareClass
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleTensor

/-! # Polarization Line -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM

noncomputable section

/-! The primitive CM generator pulls the fixed polarization line bundle
back to a fixed tensor power. The isomorphism is constructed from the
actual Rosati and Poincare equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  (D : GeneratorReconstruction.CMIntegralGeneratorData E)
  {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)

include hρ in
theorem GeneratorReconstruction.CMIntegralGeneratorData.polarizationLine_power :
    let L := PoincareClass.PoincareClasses.polarizationLine A.dual A.polarization.isogeny.hom
    Nonempty ((L.pullback (ρ.map D.generator).left).sheaf ≅
      (L.tensorPower (D.multiplier ^ 2)).sheaf) := by
  obtain ⟨q, _, hq, hp⟩ := D.rosati_similitude A ρ hρ
  let L := PoincareClass.PoincareClasses.polarizationLine A.dual A.polarization.isogeny.hom
  have h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (ρ.map D.generator).left) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower (D.multiplier ^ 2)) :=
    (PoincareClass.PoincareClasses.polarizationLine_pullback_class A.dual A.polarization.isogeny.hom
      (ρ.map D.generator) q hq (D.multiplier ^ 2) hp).trans
        (AmpleTensor.PolarizationAmpleness.tensorPower_class L (D.multiplier ^ 2)).symm
  exact Quotient.exact h

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM
