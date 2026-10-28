import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PolarizationEnhancement
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange

/-! # Enhancement Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A graph-power-compatible polarization enhancement pulls back along
every morphism of base schemes, retaining the actual power-line-bundle iso. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {S T : Scheme.{u}} {g N : ℕ}

def Level.Data.AbelianSchemeWithFullLevel.pullback (F : Level.Data.AbelianSchemeWithFullLevel g N S) (f : T ⟶ S) :
    Level.Data.AbelianSchemeWithFullLevel g N T := ⟨F.abelian.pullback f, F.level.pullback f⟩

namespace GraphPower
variable {δ : Fin g → ℕ} {F : Level.Data.AbelianSchemeWithFullLevel g N S}
variable {L : Line.Bundles.LineBundle F.abelian.scheme.left} {d : ℕ}

def PolarizationEnhancementData.GraphPowerPolarizationEnhancement.pullback (D : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F L d) (f : T ⟶ S) :
    PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ (F.pullback f)
      (L.pullback (CategoryTheory.Limits.pullback.fst F.abelian.scheme.hom f)) d where
  dual := D.dual.pullback f
  polarization := D.polarization.pullback f
  powerIso := ⟨(Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst F.abelian.scheme.hom f)).mapIso D.powerIso.some ≪≫
    D.object.graphBundle.powerBaseChangeIso (CategoryTheory.Limits.pullback.fst F.abelian.scheme.hom f) d ≪≫
      (TensorPower.Maps.tensorPowerFunctor _ d).mapIso (D.object.graphBundle_baseChangeIso f).symm⟩

theorem PolarizationEnhancementData.GraphPowerPolarizationEnhancement.pullback_object (D : PolarizationEnhancementData.GraphPowerPolarizationEnhancement δ F L d) (f : T ⟶ S) :
    (D.pullback f).object = D.object.pullback f := rfl

end GraphPower

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
