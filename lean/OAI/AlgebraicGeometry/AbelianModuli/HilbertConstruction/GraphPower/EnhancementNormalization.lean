import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.EnhancementBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.PolarizationGraphPower

/-! # Enhancement Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower

noncomputable section

/-! Compatible polarization enhancements pass to zero-normalized
line bundles without changing any component of their moduli object. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S T : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable {F : Level.Data.AbelianSchemeWithFullLevel g N S} {L M : Line.Bundles.LineBundle F.abelian.scheme.left} {d : ℕ}

def PolarizationEnhancementData.GraphPowerPolarizationEnhancement.ofBundleIso (D : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F L d) (e : M.sheaf ≅ L.sheaf) :
    PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F M d where
  dual := D.dual
  polarization := D.polarization
  powerIso := ⟨e ≪≫ D.powerIso.some⟩

def PolarizationEnhancementData.GraphPowerPolarizationEnhancement.zeroNormalize (D : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F L d) :
    PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F (F.abelian.zeroNormalizedBundle L) d where
  dual := D.dual
  polarization := D.polarization
  powerIso := by
    have h : Line.Bundles.LineBundle.classOf L = Line.Bundles.LineBundle.classOf (D.object.graphBundle.tensorPower d) :=
      Quotient.sound D.powerIso
    have hn : Line.Bundles.LineBundle.classOf (F.abelian.zeroNormalizedBundle L) =
        Line.Bundles.LineBundle.classOf (D.object.graphBundle.tensorPower d) :=
      (Line.Bundles.LineBundle.classOf_sectionNormalized F.abelian.scheme.hom η[F.abelian.scheme].left L).trans
      ((congrArg (Line.Bundles.LineBundle.sectionNormalizeClass F.abelian.scheme.hom η[F.abelian.scheme].left) h).trans
        (D.object.graphBundlePower_normalized_class d))
    exact Quotient.exact hn

theorem PolarizationEnhancementData.GraphPowerPolarizationEnhancement.zeroNormalize_object (D : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F L d) :
    D.zeroNormalize.object = D.object := rfl

def PolarizationEnhancementData.GraphPowerPolarizationEnhancement.normalizeParameter (f : T ⟶ S)
    (D : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback f)
      (L.pullback (CategoryTheory.Limits.pullback.fst F.abelian.scheme.hom f)) d) :
    PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback f)
      ((F.abelian.zeroNormalizedBundle L).pullback
        (CategoryTheory.Limits.pullback.fst F.abelian.scheme.hom f)) d :=
  D.zeroNormalize.ofBundleIso (F.abelian.zeroNormalizedBundle_baseChangeIso L f)

theorem PolarizationEnhancementData.GraphPowerPolarizationEnhancement.normalizeParameter_object (f : T ⟶ S)
    (D : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback f)
      (L.pullback (CategoryTheory.Limits.pullback.fst F.abelian.scheme.hom f)) d) :
    (D.normalizeParameter f).object = D.object := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower
