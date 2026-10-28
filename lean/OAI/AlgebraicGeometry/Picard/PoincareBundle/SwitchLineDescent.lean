import OAI.AlgebraicGeometry.Picard.PoincareBundle.SwitchCoalgebra
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.AffineDescent

/-! # Switch Line Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SwitchLineDescent

noncomputable section

/-!
# Effective geometric line descent from ordinary tensor switches for PoincareBundle
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- Ordinary tensor descent data on the global sections of an actual line bundle. -/
structure LineDatum where
  line : Line.Bundles.LineBundle (Spec S)
  descentSwitch : SwitchCoalgebra.SwitchDatum f.hom
    ((moduleSpecΓFunctor (R := S)).obj line.sheaf)

/-- The counit and cocycle fields of geometric coaction descent are proved from the switch. -/
def LineDatum.coactionDatum (D : LineDatum f) : Geometric.AffineDescent.LineDatum f where
  line := D.line
  coaction := SwitchCoalgebra.coaction f.hom _ D.descentSwitch
  counit := SwitchCoalgebra.coaction_counit f.hom _ D.descentSwitch
  coassoc := SwitchCoalgebra.coaction_coassoc f.hom _ D.descentSwitch

/-- A faithfully flat tensor descent switch produces a line bundle on the affine base. -/
def descend [IsNoetherianRing R] (hf : f.hom.FaithfullyFlat) (D : LineDatum f) :
    Line.Bundles.LineBundle (Spec R) :=
  Geometric.AffineDescent.descend f hf D.coactionDatum

/-- The geometric pullback of this constructed line bundle is the original line bundle. -/
def descendPullbackIso [IsNoetherianRing R] (hf : f.hom.FaithfullyFlat) (D : LineDatum f) :
    (Scheme.Modules.pullback (Spec.map f)).obj (descend f hf D).sheaf ≅ D.line.sheaf :=
  Geometric.AffineDescent.descendPullbackIso f hf D.coactionDatum

/-- Descent retains the full coaction extracted from the ordinary tensor switch. -/
def descendDataIso (hf : f.hom.FaithfullyFlat) (D : LineDatum f) :
    (Comonad.comparison (ModuleCat.extendRestrictScalarsAdj f.hom)).obj
        (Affine.Descent.descendedModule f.hom hf D.coactionDatum.moduleDatum) ≅
      D.coactionDatum.moduleDatum :=
  Affine.Descent.descentDataIso f.hom hf D.coactionDatum.moduleDatum

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SwitchLineDescent
