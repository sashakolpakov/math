import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PullbackSectionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.SheafBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Image
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Quasicoherence

/-! # Structure Base Change Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StructureBaseChangeValues

noncomputable section

/-! On affine schemes, the actual structure-sheaf base-change morphism sends a pure tensor to the product of the two pulled-back functions. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct
open scoped ChangeOfRings
universe u

instance affineStructurePushforward_quasicoherent {S X : Scheme.{u}}
    [IsAffine S] [IsAffine X] (f : X ⟶ S) :
    ((Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X)).IsQuasicoherent := by
  have : (Line.Bundles.structureModule X).IsQuasicoherent := (Line.Bundles.LineBundle.trivial X).isQuasicoherent
  exact Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent f (Line.Bundles.structureModule X)

variable {S X Y P : Scheme.{u}} [IsAffine S] [IsAffine X] [IsAffine Y]
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g)

theorem structureBaseChangeMap_tmul (r : Γ(Y, ⊤)) (s : Γ(X, ⊤)) :
    (Structure.SheafBaseChange.structureBaseChangeMap H).app ⊤
      ((GeometricSections.AffineGeometricSections.iso g
        ((Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X))).hom.hom
          (r ⊗ₜ[Γ(S, ⊤), g.appTop.hom] s)) =
      b.appTop r * a.appTop s := by
  refine (PullbackSectionValues.affinePullbackSections_map_tmul g _ (Structure.SheafBaseChange.structureBaseChangeMap H) r s).trans ?_
  change b.appTop r * (show Γ(P, ⊤) from
    ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      (Structure.SheafBaseChange.structureBaseChangeMap H)).app ⊤ s) = b.appTop r * a.appTop s
  apply congrArg (fun z : Γ(P, ⊤) => b.appTop r * z)
  exact (congrArg (fun φ :
      (Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X) ⟶
        (Scheme.Modules.pushforward g).obj
          ((Scheme.Modules.pushforward b).obj (Line.Bundles.structureModule P)) => φ.app ⊤ s)
    (Structure.SheafBaseChange.structureBaseChangeMap_normalization H)).trans (Structure.SheafBaseChange.structureBaseChangeAdjoint_appTop H s)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StructureBaseChangeValues
