import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PoincareSimilitude
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationLineBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.ActionGeneratorFaithfulness

/-! # CM Polarization Line -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.IntegralModel.Relative.CMPolarizationLine

/-! The canonical line on a varying polarized abelian family commutes
with every scheme base change and is ample on every geometric fiber. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

namespace RelativePoincareClasses

theorem polarizationLine_baseChange_class {S T : Scheme.{0}} {g : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (ell : A.scheme ⟶ D.abelian.scheme) (f : T ⟶ S) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (PoincareSimilitude.RelativePoincareClasses.polarizationLine (D.pullback f) ((Over.pullback f).map ell)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((PoincareSimilitude.RelativePoincareClasses.polarizationLine D ell).pullback (pullback.fst A.scheme.hom f)) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift ((Over.pullback f).map ell) (𝟙 (A.pullback f).scheme)).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (D.poincarePullbackOverMap f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (pullback.fst A.scheme.hom f)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift ell (𝟙 A.scheme)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
    PolarizationLineBaseChange.PoincareClasses.polarizationDiagonal_baseChange]

theorem polarizationLine_fiber_isAmple {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    {k : Type} [Field k] [IsAlgClosed k] (q : Spec (.of k) ⟶ S) :
    ((PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual A.polarization.isogeny.hom).pullback
      (pullback.fst A.abelian.scheme.hom q)).IsAmple := by
  have h : (PoincareSimilitude.RelativePoincareClasses.polarizationLine (A.pullback q).dual (A.pullback q).polarization.isogeny.hom).IsAmple :=
    PolarizationLineTransport.PolarizationAmpleness.polarizationLine_isAmple (A.pullback q)
  obtain ⟨e⟩ := Quotient.exact (polarizationLine_baseChange_class A.dual A.polarization.isogeny.hom q)
  exact h.of_iso e

end RelativePoincareClasses

end AlgebraicGeometry.PELModuli.IntegralModel.Relative.CMPolarizationLine

namespace AlgebraicGeometry.PELModuli.IntegralModel

/-! A primitive CM generator has the same fixed power identity for the
canonical line of a varying family, and for all new actions on geometric
fibers. The exponent is chosen from the CM order before choosing an action. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem CM.GeneratorReconstruction.CMIntegralGeneratorData.relative_polarizationLine_power
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    {S : Scheme.{0}} [IsReduced S] [IsNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) :
    let L := Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual A.polarization.isogeny.hom
    Nonempty ((L.pullback (ρ.map D.generator).left).sheaf ≅
      (L.tensorPower (D.multiplier ^ 2)).sheaf) := by
  obtain ⟨q, _, hq, hp⟩ := D.rosati_similitude A ρ hρ
  let L := Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual A.polarization.isogeny.hom
  have h := (Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine_pullback_class A.dual A.polarization.isogeny.hom
    (ρ.map D.generator) q hq (D.multiplier ^ 2) hp).trans (AmpleTensor.PolarizationAmpleness.tensorPower_class L (D.multiplier ^ 2)).symm
  exact Quotient.exact h

theorem CM.GeneratorReconstruction.CMIntegralGeneratorData.geometric_relative_polarization_power
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    {k : Type} [Field k] [IsAlgClosed k] (f : Spec (.of k) ⟶ S)
    (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left) (d : ℕ)
    (hP : AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower (Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual
      A.polarization.isogeny.hom).sheaf d P.sheaf)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback f).abelian)
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback f) ρ) :
    let Q := P.pullback (pullback.fst A.abelian.scheme.hom f)
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (ρ.map D.generator).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q ^ (D.multiplier ^ 2) := by
  let L := PoincareClass.PoincareClasses.polarizationLine (A.pullback f).dual (A.pullback f).polarization.isogeny.hom
  let Q := P.pullback (pullback.fst A.abelian.scheme.hom f)
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L ^ d := by
    change Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (pullback.fst A.abelian.scheme.hom f) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P) = _
    rw [CM.EmbeddedGraphPowers.tensorPowerWitness_class _ P d hP, map_pow]
    exact congrArg (fun c : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (A.pullback f).abelian.scheme.left => c ^ d)
      (Relative.CMPolarizationLine.RelativePoincareClasses.polarizationLine_baseChange_class A.dual A.polarization.isogeny.hom f).symm
  have hL : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (ρ.map D.generator).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L ^ (D.multiplier ^ 2) :=
    (Quotient.sound (D.polarizationLine_power (A.pullback f) ρ hρ)).trans (AmpleTensor.PolarizationAmpleness.tensorPower_class L _)
  change Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (ρ.map D.generator).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q) = _
  rw [hc, map_pow, hL, ← pow_mul, ← pow_mul, Nat.mul_comm d]

end AlgebraicGeometry.PELModuli.IntegralModel

end

end OAI
