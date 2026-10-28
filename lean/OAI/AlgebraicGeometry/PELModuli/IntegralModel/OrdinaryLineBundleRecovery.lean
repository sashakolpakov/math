import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OrdinaryLineBundleDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.SquareDescent

/-! # Ordinary Line Bundle Recovery -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.OrdinaryLineBundleRecovery

noncomputable section

/-! The constructed fpqc line recovers the entire ordinary descent
datum. Pulling this recovery through any commuting square retains the
full gluing equation, including for zero-section squares. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsAffineHom f] [IsLocallyNoetherian Y] [Flat f] [Surjective f]
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (hD : Picard.PoincareBundle.Line.Bundles.IsLine (D.obj PUnit.unit))

def fpqcDescendedLineBundleDatumIso :
    Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum f (OrdinaryLineBundleDescent.fpqcDescendedLineBundle f D hD).sheaf ≅ D :=
  Picard.PoincareBundle.Recovered.SquareDescent.originalIso f D (OrdinaryLineBundleDescent.fpqcDescendedLineBundle f D hD).sheaf
    (OrdinaryLineBundleDescent.fpqcDescendedLineBundlePullbackIso f D hD) (OrdinaryLineBundleDescent.fpqcDescendedLineBundlePullbackIso_compatible f D hD)

theorem fpqcDescendedLineBundleDatumIso_component :
    (fpqcDescendedLineBundleDatumIso f D hD).hom.hom PUnit.unit =
      (OrdinaryLineBundleDescent.fpqcDescendedLineBundlePullbackIso f D hD).hom := rfl

variable {X' Y' : Scheme.{0}} (f' : X' ⟶ Y') (iX : X' ⟶ X) (iY : Y' ⟶ Y)
    (h : iX ≫ f = f' ≫ iY)

def fpqcDescendedLineBundleSquareRecovery :
    (((OrdinaryLineBundleDescent.fpqcDescendedLineBundle f D hD).pullback iY).pullback f').sheaf ≅
      (Scheme.Modules.pullback iX).obj (D.obj PUnit.unit) :=
  Picard.PoincareBundle.Recovered.SquareDescent.pulledRecovery f f' iX iY h D (OrdinaryLineBundleDescent.fpqcDescendedLineBundle f D hD).sheaf
    (OrdinaryLineBundleDescent.fpqcDescendedLineBundlePullbackIso f D hD) (OrdinaryLineBundleDescent.fpqcDescendedLineBundlePullbackIso_compatible f D hD)

def fpqcDescendedLineBundleSquareDatumIso :
    Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum f' ((OrdinaryLineBundleDescent.fpqcDescendedLineBundle f D hD).pullback iY).sheaf ≅
      Picard.PoincareBundle.Ordinary.SquareGluing.pulledDatum f f' iX iY h D :=
  Picard.PoincareBundle.Recovered.SquareDescent.pulledIso f f' iX iY h D (OrdinaryLineBundleDescent.fpqcDescendedLineBundle f D hD).sheaf
    (OrdinaryLineBundleDescent.fpqcDescendedLineBundlePullbackIso f D hD) (OrdinaryLineBundleDescent.fpqcDescendedLineBundlePullbackIso_compatible f D hD)

theorem fpqcDescendedLineBundleSquareRecovery_compatible :
    (Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst f' f')).map
        (fpqcDescendedLineBundleSquareRecovery f D hD f' iX iY h).hom ≫
      (Picard.PoincareBundle.Geometric.CechInvariant.relationGluing f'
        (Picard.PoincareBundle.Ordinary.SquareGluing.pulledDatum f f' iX iY h D)).hom =
    (Picard.PoincareBundle.Cech.MateNormalization.standardGluing f' (CategoryTheory.Limits.pullback.fst f' f')
        (CategoryTheory.Limits.pullback.snd f' f') CategoryTheory.Limits.pullback.condition).hom.app
      ((OrdinaryLineBundleDescent.fpqcDescendedLineBundle f D hD).pullback iY).sheaf ≫
        (Scheme.Modules.pullback (CategoryTheory.Limits.pullback.snd f' f')).map
          (fpqcDescendedLineBundleSquareRecovery f D hD f' iX iY h).hom :=
  Picard.PoincareBundle.Recovered.SquareDescent.pulledRecovery_compatible f f' iX iY h D (OrdinaryLineBundleDescent.fpqcDescendedLineBundle f D hD).sheaf
    (OrdinaryLineBundleDescent.fpqcDescendedLineBundlePullbackIso f D hD) (OrdinaryLineBundleDescent.fpqcDescendedLineBundlePullbackIso_compatible f D hD)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.OrdinaryLineBundleRecovery
