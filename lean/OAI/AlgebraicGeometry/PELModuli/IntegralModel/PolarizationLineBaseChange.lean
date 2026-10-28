import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.PolarizationLine
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.EmbeddedGraphPowers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Polarization Line Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The canonical polarization line is compatible with actual scheme base
change. Consequently the fixed tensor-power identity applies also to new
Rosati-compatible actions acquired after an algebraically closed extension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

namespace PolarizationLineBaseChange.PoincareClasses

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

theorem polarizationDiagonal_baseChange {S T : Scheme.{0}} {g : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (ell : A.scheme ⟶ D.abelian.scheme) (f : T ⟶ S) :
    (lift ((Over.pullback f).map ell) (𝟙 (A.pullback f).scheme)).left ≫
        (D.poincarePullbackOverMap f).left =
      pullback.fst A.scheme.hom f ≫ (lift ell (𝟙 A.scheme)).left := by
  have hfst : (lift ((Over.pullback f).map ell) (𝟙 (A.pullback f).scheme)).left ≫
      pullback.fst (D.abelian.pullback f).scheme.hom (A.pullback f).scheme.hom =
        ((Over.pullback f).map ell).left :=
    congrArg Over.Hom.left (lift_fst ((Over.pullback f).map ell) (𝟙 (A.pullback f).scheme))
  have hsnd : (lift ((Over.pullback f).map ell) (𝟙 (A.pullback f).scheme)).left ≫
      pullback.snd (D.abelian.pullback f).scheme.hom (A.pullback f).scheme.hom = 𝟙 _ :=
    congrArg Over.Hom.left (lift_snd ((Over.pullback f).map ell) (𝟙 (A.pullback f).scheme))
  have hfst₀ : (lift ell (𝟙 A.scheme)).left ≫
      pullback.fst D.abelian.scheme.hom A.scheme.hom = ell.left :=
    congrArg Over.Hom.left (lift_fst ell (𝟙 A.scheme))
  have hsnd₀ : (lift ell (𝟙 A.scheme)).left ≫
      pullback.snd D.abelian.scheme.hom A.scheme.hom = 𝟙 _ :=
    congrArg Over.Hom.left (lift_snd ell (𝟙 A.scheme))
  apply Over.tensorObj_ext
  · rw [Category.assoc, D.poincarePullbackOverMap_left_fst,
      ← Category.assoc, hfst, AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst, Category.assoc, hfst₀]
  · rw [Category.assoc, D.poincarePullbackOverMap_left_snd,
      ← Category.assoc, hsnd, Category.id_comp, Category.assoc, hsnd₀, Category.comp_id]

theorem polarizationLine_baseChange_class {k K : Type} [Field k] [Field K] {g : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (ell : A.scheme ⟶ D.abelian.scheme) (f : Spec (.of K) ⟶ Spec (.of k)) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (PoincareClass.PoincareClasses.polarizationLine (D.pullback f) ((Over.pullback f).map ell)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((PoincareClass.PoincareClasses.polarizationLine D ell).pullback (pullback.fst A.scheme.hom f)) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift ((Over.pullback f).map ell) (𝟙 (A.pullback f).scheme)).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (D.poincarePullbackOverMap f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (pullback.fst A.scheme.hom f)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift ell (𝟙 A.scheme)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
    polarizationDiagonal_baseChange]

end PolarizationLineBaseChange.PoincareClasses

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationLineBaseChange.PoincareClasses

theorem CM.GeneratorReconstruction.CMIntegralGeneratorData.baseChanged_polarization_power
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    {k K : Type} [Field k] [Field K] [IsAlgClosed K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
    (f : Spec (.of K) ⟶ Spec (.of k))
    (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left) (d : ℕ)
    (hP : AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower (PoincareClass.PoincareClasses.polarizationLine A.dual A.polarization.isogeny.hom).sheaf d P.sheaf)
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
      (PolarizationLineBaseChange.PoincareClasses.polarizationLine_baseChange_class A.dual A.polarization.isogeny.hom f).symm
  have hL : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (ρ.map D.generator).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L ^ (D.multiplier ^ 2) :=
    (Quotient.sound (D.polarizationLine_power (A.pullback f) ρ hρ)).trans
      (AmpleTensor.PolarizationAmpleness.tensorPower_class L (D.multiplier ^ 2))
  change Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (ρ.map D.generator).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q) = _
  rw [hc, map_pow, hL, ← pow_mul, ← pow_mul, Nat.mul_comm d]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
