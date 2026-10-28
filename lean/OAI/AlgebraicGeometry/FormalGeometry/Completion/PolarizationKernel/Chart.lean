import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Polarization.FamilyBundle
import OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalFrameTriviality

/-! # Chart -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Chart

noncomputable section

/-! Over an affine Noetherian parameter scheme, the actual polarization
kernel condition is represented by a finite-type monomorphism. The
projective presentation, line bundle, and rigidification are all derived. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) {T : Over (Spec (CommRingCat.of K))}
  [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] (a : T ⟶ A)

instance tensorFamilyOver_flat : Flat (Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom :=
  inferInstanceAs (Flat (pullback.fst T.hom A.hom))

def polarizationFamilyAxis : T.left ⟶ (T ⊗ A).left := (lift (𝟙 T) (1 : T ⟶ A)).left

omit [IsAlgClosed K] [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] in
theorem polarizationFamilyAxis_section :
    polarizationFamilyAxis A (T := T) ≫ (Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom = 𝟙 T.left :=
  congrArg Over.Hom.left (lift_fst (𝟙 T) (1 : T ⟶ A))

def polarizationKernelChart : Over T.left :=
  Projective.RigidifiedFrames.Construction.projectiveLineBundleRigidifiedFrameScheme (Projective.ConstantFamily.Construction.tensorFamilyOver A T)
    (Projective.ConstantFamily.Construction.geometricGroupFamilyProjectivePresentation A T) (Polarization.FamilyBundle.Construction.polarizationFamilyBundle A L a)
    (polarizationFamilyAxis A) (polarizationFamilyAxis_section A) (Polarization.FamilyBundle.Construction.polarizationFamilyRigidification A L a)

instance polarizationKernelChart_locallyOfFiniteType : LocallyOfFiniteType (polarizationKernelChart A L a).hom :=
  inferInstanceAs (LocallyOfFiniteType (Projective.RigidifiedFrames.Construction.projectiveLineBundleRigidifiedFrameScheme (Projective.ConstantFamily.Construction.tensorFamilyOver A T)
    (Projective.ConstantFamily.Construction.geometricGroupFamilyProjectivePresentation A T) (Polarization.FamilyBundle.Construction.polarizationFamilyBundle A L a)
    (polarizationFamilyAxis A) (polarizationFamilyAxis_section A) (Polarization.FamilyBundle.Construction.polarizationFamilyRigidification A L a)).hom)

instance polarizationKernelChart_quasiCompact : QuasiCompact (polarizationKernelChart A L a).hom :=
  inferInstanceAs (QuasiCompact (Projective.RigidifiedFrames.Construction.projectiveLineBundleRigidifiedFrameScheme (Projective.ConstantFamily.Construction.tensorFamilyOver A T)
    (Projective.ConstantFamily.Construction.geometricGroupFamilyProjectivePresentation A T) (Polarization.FamilyBundle.Construction.polarizationFamilyBundle A L a)
    (polarizationFamilyAxis A) (polarizationFamilyAxis_section A) (Polarization.FamilyBundle.Construction.polarizationFamilyRigidification A L a)).hom)

instance polarizationKernelChart_mono : Mono (polarizationKernelChart A L a).hom := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  exact Projective.RigidifiedFrames.Construction.projectiveLineBundleRigidifiedFrameScheme_mono (Projective.ConstantFamily.Construction.tensorFamilyOver A T)
    (Projective.ConstantFamily.Construction.geometricGroupFamilyProjectivePresentation A T) (Polarization.FamilyBundle.Construction.polarizationFamilyBundle A L a)
    (polarizationFamilyAxis A) (polarizationFamilyAxis_section A) (Polarization.FamilyBundle.Construction.polarizationFamilyRigidification A L a)
    A.hom (snd T A).left T.hom (IsPullback.of_hasPullback T.hom A.hom).flip

theorem polarizationKernelChart_hasLift_iff {U : Over (Spec (CommRingCat.of K))} (j : U ⟶ T) :
    Nonempty (Over.mk j.left ⟶ polarizationKernelChart A L a) ↔
      Polarization.Family.Construction.polarizationFamilyClass A L (j ≫ a) = 0 := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have hc := GlobalFrameTriviality.Construction.projectiveLineBundleRigidifiedFrame_hasPoint_iff_trivialClass A.hom
    (Projective.ConstantFamily.Construction.tensorFamilyOver A T) (Projective.ConstantFamily.Construction.geometricGroupFamilyProjectivePresentation A T)
    (snd T A).left T.hom (IsPullback.of_hasPullback T.hom A.hom).flip
    (Polarization.FamilyBundle.Construction.polarizationFamilyBundle A L a) (polarizationFamilyAxis A) (polarizationFamilyAxis_section A)
    (Polarization.FamilyBundle.Construction.polarizationFamilyRigidification A L a) (j ⊗ₘ 𝟙 A).left (fst U A).left j.left (Projective.ConstantFamily.Construction.tensorFamily_isPullback A T j)
  refine hc.trans ?_
  rw [Polarization.FamilyBundle.Construction.polarizationFamilyBundle_pullback]
  constructor
  · intro h
    exact Additive.toMul.injective h
  · intro h
    exact congrArg Additive.toMul h

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Chart
