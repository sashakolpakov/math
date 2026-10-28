import OAI.RepresentationTheory.Theta.Geometric.MonoResidueFields
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeLocalEquations
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeTriviality

/-! # Relative Fiber Triviality -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFiberTriviality.Geometric.RelativeRigidifiedCharts

noncomputable section

/-! An actual point of the Picard zero scheme supplies triviality on
the entire corresponding geometric family fiber, including after local base change. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.RepresentationTheory.Theta.Geometric.MonoResidueFields

variable {S : Scheme} {A B T : Over S} [GrpObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [IsLocallyNoetherian B.left] (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A) (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)
    (a : T ⟶ B) (y : T.left) (z : (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).left)
    (h : a.left y = (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom z)

include h in
theorem zeroScheme_fiber_trivial :
    Nonempty ((Scheme.Modules.pullback ((FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom.fiberι y)).obj
      (D.line a).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom.fiber y)) := by
  let U : Over S := Over.mk (T.left.fromSpecResidueField y ≫ T.hom)
  let j : U ⟶ T := Over.homMk (T.left.fromSpecResidueField y) rfl
  obtain ⟨w, hw⟩ := RepresentationTheory.Theta.Geometric.MonoResidueFields.residuePoint_hasLift (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom a.left y z h
  have hz : D.relativeValue (j ≫ a) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A U :=
    (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme_hasLift_iff D P (j ≫ a)).mp ⟨Over.homMk w hw⟩
  let : IsLocallyNoetherian U.left := inferInstanceAs (IsLocallyNoetherian (Spec (T.left.residueField y)))
  have hc := RelativeTriviality.Geometric.noetherian_relativeRigidified_class_trivial D (j ≫ a) hz
  have he : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (j ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (U ⊗ A).left := (D.line_class_pullback j a).trans hc
  obtain ⟨e⟩ := Quotient.exact he
  let hp := FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamily_isPullback A T j
  let c := hp.isoPullback
  exact ⟨(Scheme.Modules.pullbackCongr hp.isoPullback_inv_fst.symm).app (D.line a).sheaf ≪≫
    ((Scheme.Modules.pullbackComp c.inv (j ⊗ₘ 𝟙 A).left).app (D.line a).sheaf).symm ≪≫
    (Scheme.Modules.pullback c.inv).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso c.inv⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFiberTriviality.Geometric.RelativeRigidifiedCharts
