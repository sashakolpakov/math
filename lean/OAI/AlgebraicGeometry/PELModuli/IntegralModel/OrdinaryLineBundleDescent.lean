import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Ordinary Line Bundle Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.OrdinaryLineBundleDescent

noncomputable section

/-! Effective descent of an actual ordinary line-bundle cocycle into
the native HilbertConstruction line-bundle interface. The support constructs the invariant
sheaf and proves recovery; no effectivity premise is used. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsAffineHom f] [IsLocallyNoetherian Y] [Flat f] [Surjective f]
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (hD : Picard.PoincareBundle.Line.Bundles.IsLine (D.obj PUnit.unit))

def fpqcDescendedLineBundle : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y :=
  let L := Picard.PoincareBundle.Ordinary.GlobalLineDescent.descendedLine f D hD
  ⟨L.sheaf, L.isLine⟩

def fpqcDescendedLineBundlePullbackIso :
    ((fpqcDescendedLineBundle f D hD).pullback f).sheaf ≅ D.obj PUnit.unit :=
  Picard.PoincareBundle.Ordinary.GlobalLineDescent.descendedLinePullbackIso f D hD

theorem fpqcDescendedLineBundlePullbackIso_compatible :
    (Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst f f)).map
        (fpqcDescendedLineBundlePullbackIso f D hD).hom ≫
          (Picard.PoincareBundle.Geometric.CechInvariant.relationGluing f D).hom =
      (Picard.PoincareBundle.Cech.MateNormalization.standardGluing f (CategoryTheory.Limits.pullback.fst f f)
        (CategoryTheory.Limits.pullback.snd f f) CategoryTheory.Limits.pullback.condition).hom.app
          (fpqcDescendedLineBundle f D hD).sheaf ≫
        (Scheme.Modules.pullback (CategoryTheory.Limits.pullback.snd f f)).map
          (fpqcDescendedLineBundlePullbackIso f D hD).hom :=
  Picard.PoincareBundle.Ordinary.GlobalLineDescent.descendedLinePullbackIso_compatible f D hD

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.OrdinaryLineBundleDescent
