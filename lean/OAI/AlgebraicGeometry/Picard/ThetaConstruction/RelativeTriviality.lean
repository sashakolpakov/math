import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeZeroCharts
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.BundleNormalization

/-! # Relative Triviality -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeTriviality.Geometric

noncomputable section

/-! Zero in the original relative Picard sheaf gives an actual
trivialization of a rigidified line. On Noetherian tests this follows
from descent; an original projective presentation gives all tests. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.BundleNormalization.Construction

variable {S : Scheme} {A B : Over S} [GrpObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)

theorem noetherian_relativeRigidified_class_trivial {T : Over S} [IsLocallyNoetherian T.left]
    (a : T ⟶ B) (h : D.relativeValue a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (T ⊗ A).left := by
  let y := RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.axis (A := A) T
  have hy : y ≫ pullback.fst T.hom A.hom = 𝟙 T.left := RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.axis_section T
  let d : (Scheme.Modules.pullback y).obj (D.line a).sheaf ≅
      (Scheme.Modules.pullback y).obj (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial (T ⊗ A).left).sheaf :=
    D.frame a ≪≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso y).symm
  exact Quotient.sound (AbelianScheme.IsogenyQuotient.Noetherian.PicardClassIso.Construction.noetherian_bundleIso_of_relativePicard_eq A T
    (D.line a) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial (T ⊗ A).left) y hy d h)

theorem projectiveFamily_hasUniversalGlobalFunctions [IsLocallyNoetherian S]
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A) : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions A := by
  intro T b
  exact AbelianModuli.HilbertConstruction.Projective.UniversalGlobalFunctions.projectivePresentation_baseChange_globalFunctions_isIso P η[A].left η[A].w
    (IsPullback.of_hasPullback A.hom b)

theorem relativeProjective_rigidified_class_trivial [IsLocallyNoetherian S]
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A) {T : Over S} (a : T ⟶ B)
    (h : D.relativeValue a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (T ⊗ A).left := by
  let y := RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.axis (A := A) T
  have hy : y ≫ pullback.fst T.hom A.hom = 𝟙 T.left := RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.axis_section T
  let d : (Scheme.Modules.pullback y).obj (D.line a).sheaf ≅
      (Scheme.Modules.pullback y).obj (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial (T ⊗ A).left).sheaf :=
    D.frame a ≪≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso y).symm
  exact Quotient.sound (AbelianScheme.IsogenyQuotient.Universal.BundleNormalization.Construction.universal_bundleIso_of_relativePicard_eq A T
    (projectiveFamily_hasUniversalGlobalFunctions P) (D.line a)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial (T ⊗ A).left) y hy d h)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeTriviality.Geometric
