import OAI.RepresentationTheory.Theta.Geometric.MonoResidueFields
import OAI.RepresentationTheory.Theta.Geometric.Picard.ZeroSchemeLocalEquations
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.RelativeZeroTriviality

/-! # Zero Fiber Triviality -/

namespace OAI.RepresentationTheory.Theta.Geometric.Picard.ZeroFiberTriviality

noncomputable section

/-! An actual point of the Picard zero scheme supplies triviality on
the entire corresponding geometric family fiber, including after local base change. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
    {A B T : Over (Spec (.of K))} [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
    [IsLocallyNoetherian B.left] (D : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A B)
    (a : T ⟶ B) (y : T.left) (z : D.zeroScheme.left)
    (h : a.left y = D.zeroScheme.hom z)

include h in
theorem picard_zeroScheme_fiber_trivial :
    Nonempty ((Scheme.Modules.pullback ((AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom.fiberι y)).obj
      (D.line a).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom.fiber y)) := by
  let U : Over (Spec (.of K)) := Over.mk (T.left.fromSpecResidueField y ≫ T.hom)
  let j : U ⟶ T := Over.homMk (T.left.fromSpecResidueField y) rfl
  obtain ⟨w, hw⟩ := MonoResidueFields.residuePoint_hasLift D.zeroScheme.hom a.left y z h
  have hz : D.relativeValue (j ≫ a) = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A U :=
    (D.zeroScheme_hasLift_iff (j ≫ a)).mp ⟨Over.homMk w hw⟩
  have hc := D.class_trivial_of_relative_zero (j ≫ a) hz
  have he : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (j ⊗ₘ 𝟙 A).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a)) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (U ⊗ A).left := (D.line_class_pullback j a).trans hc
  obtain ⟨e⟩ := Quotient.exact he
  let hp := AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamily_isPullback A T j
  let c := hp.isoPullback
  exact ⟨(Scheme.Modules.pullbackCongr hp.isoPullback_inv_fst.symm).app (D.line a).sheaf ≪≫
    ((Scheme.Modules.pullbackComp c.inv (j ⊗ₘ 𝟙 A).left).app (D.line a).sheaf).symm ≪≫
    (Scheme.Modules.pullback c.inv).mapIso e ≪≫ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso c.inv⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Picard.ZeroFiberTriviality
