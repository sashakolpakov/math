import OAI.AlgebraicGeometry.Quotients.FiniteDescent.MonoidalLine
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvertibleProjectionTensor
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperModification

/-! # Picard -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.Picard.Construction.PicardDescent

noncomputable section

/-! Line-bundle classes descend faithfully when the pushforward of the
structure sheaf is the structure sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory SheafCohomology.Projective.Monoidal.Scheme.Modules.symmetricCategory

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable (hO : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pushforward f).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X))

def trivial (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (hL : (L.pullback f).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :
    L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y := by
  let := SheafCohomology.Projective.PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f
  let hG := (Scheme.Modules.pushforward f).mapIso (MonoidalLine.Construction.MonoidalLineBundles.unitIso X) ≪≫
    hO.symm ≪≫ (MonoidalLine.Construction.MonoidalLineBundles.unitIso Y).symm
  exact InvertibleProjectionTensor.Construction.InvertibleProjection.descend_trivial (Scheme.Modules.pullback f)
    (Scheme.Modules.pushforward f) (Scheme.Modules.pullbackPushforwardAdjunction f)
    L.sheaf (DualLine.Construction.DualLineBundle.dual L).sheaf
    (MonoidalLine.Construction.MonoidalLineBundles.evaluation L) (MonoidalLine.Construction.MonoidalLineBundles.evaluation_swap L) hG
    (hL ≪≫ (MonoidalLine.Construction.MonoidalLineBundles.unitIso X).symm) ≪≫ MonoidalLine.Construction.MonoidalLineBundles.unitIso Y

include hO

theorem class_eq_one (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass Y)
    (hq : PicardPullbackId.Construction.PicardPullback.map f q = 1) : q = 1 := by
  induction q using Quotient.inductionOn with
  | h L =>
    have he : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback f) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X) := hq
    obtain ⟨e⟩ := Quotient.exact he
    exact Quotient.sound ⟨trivial f hO L e⟩

theorem injective : Function.Injective (PicardPullbackId.Construction.PicardPullback.map f) := by
  intro q r hqr
  apply div_eq_one.mp
  apply class_eq_one f hO
  rw [map_div, hqr, div_self']

theorem iso_of_pullback_iso (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (e : (L.pullback f).sheaf ≅ (M.pullback f).sheaf) : Nonempty (L.sheaf ≅ M.sheaf) := by
  have he : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback f) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (M.pullback f) :=
    Quotient.sound ⟨e⟩
  have hLM : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M := injective f hO he
  exact Quotient.exact hLM

omit hO in
theorem modification_injective [IsIntegral X] [IsIntegral Y] [IsProper f]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) [Nonempty U] [IsIso (f ∣_ U)] :
    Function.Injective (PicardPullbackId.Construction.PicardPullback.map f) :=
  injective f (ProperModification.Construction.ProperModificationFunctions.iso hY f U)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.Picard.Construction.PicardDescent
