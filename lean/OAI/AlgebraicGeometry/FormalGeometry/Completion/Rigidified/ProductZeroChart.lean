import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductPicard
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily
import OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalFrameTriviality
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Chart

/-! # Product Zero Chart -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified

noncomputable section

/-! The actual zero locus of a rigidified family has finite-type
normalized-frame charts, with no restriction on the test schemes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  {A B : Over (Spec (.of K))} [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (D : ProductLine.Construction.RigidifiedProductLine A B) {T : Over (Spec (.of K))}
  [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] (a : T ⟶ B)

def ProductLine.Construction.RigidifiedProductLine.zeroChart : Over T.left :=
  Projective.RigidifiedFrames.Construction.projectiveLineBundleRigidifiedFrameScheme (Projective.ConstantFamily.Construction.tensorFamilyOver A T)
    (Projective.ConstantFamily.Construction.geometricGroupFamilyProjectivePresentation A T) (D.line a)
    (PolarizationKernel.Chart.Construction.polarizationFamilyAxis A) (PolarizationKernel.Chart.Construction.polarizationFamilyAxis_section A) (D.frame a)

instance ProductLine.Construction.RigidifiedProductLine.zeroChart_locallyOfFiniteType : LocallyOfFiniteType (D.zeroChart a).hom :=
  inferInstanceAs (LocallyOfFiniteType (Projective.RigidifiedFrames.Construction.projectiveLineBundleRigidifiedFrameScheme (Projective.ConstantFamily.Construction.tensorFamilyOver A T)
    (Projective.ConstantFamily.Construction.geometricGroupFamilyProjectivePresentation A T) (D.line a)
    (PolarizationKernel.Chart.Construction.polarizationFamilyAxis A) (PolarizationKernel.Chart.Construction.polarizationFamilyAxis_section A) (D.frame a)).hom)

instance ProductLine.Construction.RigidifiedProductLine.zeroChart_quasiCompact : QuasiCompact (D.zeroChart a).hom :=
  inferInstanceAs (QuasiCompact (Projective.RigidifiedFrames.Construction.projectiveLineBundleRigidifiedFrameScheme (Projective.ConstantFamily.Construction.tensorFamilyOver A T)
    (Projective.ConstantFamily.Construction.geometricGroupFamilyProjectivePresentation A T) (D.line a)
    (PolarizationKernel.Chart.Construction.polarizationFamilyAxis A) (PolarizationKernel.Chart.Construction.polarizationFamilyAxis_section A) (D.frame a)).hom)

instance ProductLine.Construction.RigidifiedProductLine.zeroChart_mono : Mono (D.zeroChart a).hom := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  exact Projective.RigidifiedFrames.Construction.projectiveLineBundleRigidifiedFrameScheme_mono (Projective.ConstantFamily.Construction.tensorFamilyOver A T)
    (Projective.ConstantFamily.Construction.geometricGroupFamilyProjectivePresentation A T) (D.line a)
    (PolarizationKernel.Chart.Construction.polarizationFamilyAxis A) (PolarizationKernel.Chart.Construction.polarizationFamilyAxis_section A) (D.frame a)
    A.hom (snd T A).left T.hom (IsPullback.of_hasPullback T.hom A.hom).flip

theorem ProductLine.Construction.RigidifiedProductLine.zeroChart_hasLift_iff_class {U : Over (Spec (.of K))} (j : U ⟶ T) :
    Nonempty (Over.mk j.left ⟶ D.zeroChart a) ↔
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line (j ≫ a)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (U ⊗ A).left := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have hc := GlobalFrameTriviality.Construction.projectiveLineBundleRigidifiedFrame_hasPoint_iff_trivialClass A.hom
    (Projective.ConstantFamily.Construction.tensorFamilyOver A T) (Projective.ConstantFamily.Construction.geometricGroupFamilyProjectivePresentation A T)
    (snd T A).left T.hom (IsPullback.of_hasPullback T.hom A.hom).flip
    (D.line a) (PolarizationKernel.Chart.Construction.polarizationFamilyAxis A) (PolarizationKernel.Chart.Construction.polarizationFamilyAxis_section A)
    (D.frame a) (j ⊗ₘ 𝟙 A).left (fst U A).left j.left (Projective.ConstantFamily.Construction.tensorFamily_isPullback A T j)
  exact hc.trans (by rw [D.line_class_pullback])

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified
