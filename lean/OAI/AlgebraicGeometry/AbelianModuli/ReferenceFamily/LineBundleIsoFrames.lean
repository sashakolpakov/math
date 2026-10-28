import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorEquivalence
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.DualEvaluationIs
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorBaseChange

/-! # Line Bundle Iso Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineBundleIsoFrames

noncomputable section

/-! Actual isomorphisms of line bundles are equivalent to actual
frames of their tensor difference, including after arbitrary base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorEquivalence

universe u v

def lineIsoTransportEquiv {C : Type u} [Category.{v} C] {X X' Y Y' : C}
    (e : X ≅ X') (f : Y ≅ Y') : (X ≅ Y) ≃ (X' ≅ Y') where
  toFun h := e.symm ≪≫ h ≪≫ f
  invFun h := e ≪≫ h ≪≫ f.symm
  left_inv h := by ext; simp
  right_inv h := by ext; simp

variable {X Y : Scheme.{u}}

def lineBundleIsoFrameEquivOfPairing (L K D : HilbertConstruction.Line.Bundles.LineBundle X)
    (e : (L.tensor D).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule X) :
    (L.sheaf ≅ K.sheaf) ≃ (HilbertConstruction.Line.Bundles.structureModule X ≅ (K.tensor D).sheaf) := by
  let : MonoidalCategory X.Modules := SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X
  let F := SheafCohomology.Projective.InvertibleTensorEquivalence.invertibleRightTensorEquivalence D.sheaf (Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible D)
  let eL : F.functor.obj L.sheaf ≅ HilbertConstruction.Line.Bundles.structureModule X :=
    SheafCohomology.Projective.TensorSections.monoidalTensorObjIso L.sheaf D.sheaf ≪≫ e
  let eK : F.functor.obj K.sheaf ≅ (K.tensor D).sheaf := SheafCohomology.Projective.TensorSections.monoidalTensorObjIso K.sheaf D.sheaf
  exact F.fullyFaithfulFunctor.isoEquiv.trans (lineIsoTransportEquiv eL eK)

def lineBundleDifference (L K : HilbertConstruction.Line.Bundles.LineBundle X) : HilbertConstruction.Line.Bundles.LineBundle X :=
  K.tensor (Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dual L)

def lineBundleIsoFrameEquiv (L K : HilbertConstruction.Line.Bundles.LineBundle X) :
    (L.sheaf ≅ K.sheaf) ≃ (HilbertConstruction.Line.Bundles.structureModule X ≅ (lineBundleDifference L K).sheaf) :=
  lineBundleIsoFrameEquivOfPairing L K (Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dual L) (Quotients.FiniteDescent.DualEvaluationIs.Construction.DualEvaluation.iso L)

def pulledLineBundleIsoFrameEquiv (f : Y ⟶ X) (L K : HilbertConstruction.Line.Bundles.LineBundle X) :
    ((L.pullback f).sheaf ≅ (K.pullback f).sheaf) ≃
      (HilbertConstruction.Line.Bundles.structureModule Y ≅ ((lineBundleDifference L K).pullback f).sheaf) := by
  let D := Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dual L
  let e : ((L.pullback f).tensor (D.pullback f)).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule Y :=
    (HilbertConstruction.Line.Bundles.LineBundle.tensorBaseChangeIso f L D).symm ≪≫
      (Scheme.Modules.pullback f).mapIso (Quotients.FiniteDescent.DualEvaluationIs.Construction.DualEvaluation.iso L) ≪≫
        HilbertConstruction.Line.Bundles.structureModulePullbackIso f
  exact (lineBundleIsoFrameEquivOfPairing (L.pullback f) (K.pullback f) (D.pullback f) e).trans
    (lineIsoTransportEquiv (Iso.refl _) (HilbertConstruction.Line.Bundles.LineBundle.tensorBaseChangeIso f K D).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineBundleIsoFrames
