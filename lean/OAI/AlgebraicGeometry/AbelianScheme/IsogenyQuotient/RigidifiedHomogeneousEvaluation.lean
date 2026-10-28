import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.HomogeneousPicardEvaluation

/-! # Rigidified Homogeneous Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedHomogeneousEvaluation.Construction

noncomputable section

/-! A normalized homogeneous product family evaluates multiplicatively
in the group coordinate as an identity of actual line-bundle classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k] {A C : Over (Spec (.of k))} [GrpObj A]
  (Q : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A C)
  {T : Over (Spec (.of k))} (x : T ⟶ C) (a : T ⟶ A)

set_option backward.isDefEq.respectTransparency false in
theorem rigidifiedFamily_evaluation_class :
    HomogeneousPicardEvaluation.Construction.nativeHomogeneous_evaluateClass A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.line x)) a =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift x a).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q.bundle) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (HomogeneousPicardEvaluation.Construction.homogeneousEvaluationSection A a).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (x ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q.bundle)) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  have h : HomogeneousPicardEvaluation.Construction.homogeneousEvaluationSection A a ≫ (x ⊗ₘ 𝟙 A) = lift x a := by
    simp [HomogeneousPicardEvaluation.Construction.homogeneousEvaluationSection]
  exact congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q.bundle))
    (congrArg Over.Hom.left h)

variable [IsAlgClosed k] [IsCommMonObj A] [IsProper A.hom] [Smooth A.hom]
  [GeometricallyIntegral A.hom] [IsLocallyNoetherian T.left]
  (hQ : Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A C (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q.bundle))

include hQ in
set_option backward.isDefEq.respectTransparency false in
theorem rigidifiedFamily_pointClass_mul (b : T ⟶ A) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift x (a * b)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q.bundle) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift x a).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q.bundle) *
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift x b).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q.bundle) := by
  have hc : Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A T (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.line x)) := hQ.pullback A x
  have hzero : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (lift (𝟙 T) (1 : T ⟶ A)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.line x)) = 1 :=
    Quotient.sound ⟨Q.frame x⟩
  have h := HomogeneousPicardEvaluation.Construction.nativeHomogeneous_evaluateClass_mul A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.line x)) hc hzero a b
  rw [rigidifiedFamily_evaluation_class, rigidifiedFamily_evaluation_class,
    rigidifiedFamily_evaluation_class] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedHomogeneousEvaluation.Construction
