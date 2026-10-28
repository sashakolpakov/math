import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFrameClassification
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.RigidifiedNaturality
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily

/-! # Relative Zero Charts -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeZeroCharts.Geometric.RelativeRigidifiedCharts

noncomputable section

/-! The zero class of a rigidified line on a varying projective group
family has an actual finite-type normalized-frame chart. Classification
retains every test scheme over the original parameter scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction

variable {S : Scheme} {A B : Over S} [GrpObj A]

def axis (T : Over S) : T.left ⟶ (T ⊗ A).left := (lift (𝟙 T) (1 : T ⟶ A)).left

theorem axis_section (T : Over S) :
    axis (A := A) T ≫ (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom = 𝟙 T.left :=
  congrArg Over.Hom.left (lift_fst (𝟙 T) (1 : T ⟶ A))

local instance tensorFamily_proper [IsProper A.hom] (T : Over S) : IsProper (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom :=
  inferInstanceAs (IsProper (pullback.fst T.hom A.hom))
local instance tensorFamily_smooth [Smooth A.hom] (T : Over S) : Smooth (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom :=
  inferInstanceAs (Smooth (pullback.fst T.hom A.hom))
local instance tensorFamily_connected [GeometricallyConnected A.hom] (T : Over S) : GeometricallyConnected (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom :=
  inferInstanceAs (GeometricallyConnected (pullback.fst T.hom A.hom))
local instance tensorFamily_flat [Flat A.hom] (T : Over S) : Flat (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom :=
  inferInstanceAs (Flat (pullback.fst T.hom A.hom))

variable [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A) (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)
    {T : Over S} [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)]
    [IsLocallyNoetherian T.left] (a : T ⟶ B)

def zeroChart : Over T.left :=
  FormalGeometry.Completion.Projective.RigidifiedFrames.Construction.projectiveLineBundleRigidifiedFrameScheme (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T)
    (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyProjectivePresentation A T P) (D.line a)
    (axis T) (axis_section T) (D.frame a)

instance zeroChart_locallyOfFiniteType : LocallyOfFiniteType (zeroChart P D a).hom :=
  FormalGeometry.Completion.Projective.RigidifiedFrames.Construction.projectiveLineBundleRigidifiedFrameScheme_locallyOfFiniteType
    (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T) (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyProjectivePresentation A T P) (D.line a)
    (axis T) (axis_section T) (D.frame a)

instance zeroChart_quasiCompact : QuasiCompact (zeroChart P D a).hom :=
  FormalGeometry.Completion.Projective.RigidifiedFrames.Construction.projectiveLineBundleRigidifiedFrameScheme_quasiCompact
    (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T) (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyProjectivePresentation A T P) (D.line a)
    (axis T) (axis_section T) (D.frame a)

instance zeroChart_mono : Mono (zeroChart P D a).hom :=
  RelativeFrameClassification.Geometric.relativeProjective_projectiveRigidifiedFrame_mono (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyProjectivePresentation A T P)
    (axis T) (axis_section T) (D.frame a)

theorem zeroChart_hasLift_iff_class {U : Over S} (j : U ⟶ T) :
    Nonempty (Over.mk j.left ⟶ zeroChart P D a) ↔
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line (j ≫ a)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (U ⊗ A).left := by
  have hc := RelativeFrameClassification.Geometric.relativeProjective_projectiveRigidifiedFrame_hasPoint_iff_trivialClass
    (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyProjectivePresentation A T P) (axis T) (axis_section T) (D.frame a)
    (j ⊗ₘ 𝟙 A).left (fst U A).left j.left (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamily_isPullback A T j)
  exact hc.trans ⟨fun h => (D.line_class_pullback j a).symm.trans h,
    fun h => (D.line_class_pullback j a).trans h⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeZeroCharts.Geometric.RelativeRigidifiedCharts
