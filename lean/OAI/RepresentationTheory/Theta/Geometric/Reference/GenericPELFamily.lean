import OAI.RepresentationTheory.Theta.Geometric.Reference.ModuliPoints
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotientFibers
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CorrespondencePointBaseChange

/-! # Generic PEL Family -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Original reference classifying points and their complete PEL families
are transported to the actual generic-fiber correspondence interface. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CorrespondencePointBaseChange

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {x : D.domain}

def Data.ActiveHeckeThetaData.complexGenericPointEquiv : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace ≃
    D.pel.GeometricPoint (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint) :=
  AlgebraicGeometry.AbelianScheme.TateComparison.FieldPointTransport.pointBaseChangeEquiv D.pel.complexGenericPoint (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint) rfl D.pel.space

def Data.ActiveHeckeThetaData.complexGenericFamilyIso (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace) :
    AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso
      (D.pel.fiberFamily (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint) (Data.ActiveHeckeThetaData.complexGenericPointEquiv p))
      (D.pel.model.family.pullback (Complex.PELClassification.modelComplexPointEquiv D.pel p).left) := by
  have he : (Data.ActiveHeckeThetaData.complexGenericPointEquiv p).left ≫ Limits.pullback.fst D.pel.model.space.hom D.pel.generic =
      (Complex.PELClassification.modelComplexPointEquiv D.pel p).left := by
    rw [Complex.PELClassification.modelComplexPointEquiv_left]
    change (AlgebraicGeometry.AbelianScheme.TateComparison.FieldPointTransport.pointBaseChangeEquiv D.pel.complexGenericPoint (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
      (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint) rfl D.pel.space p).left ≫ _ = _
    rw [AlgebraicGeometry.AbelianScheme.TateComparison.FieldPointTransport.pointBaseChangeEquiv_left, Category.assoc]
  exact (D.pel.model.family.pullbackFactor (Data.ActiveHeckeThetaData.complexGenericPointEquiv p).left
    (Limits.pullback.fst D.pel.model.space.hom D.pel.generic)
    (Complex.PELClassification.modelComplexPointEquiv D.pel p).left he).symm

variable (R : D.ReferencePELPointData hg x)

def Data.ActiveHeckeThetaData.ReferencePELPointData.genericPoint : D.pel.GeometricPoint (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint) :=
  Data.ActiveHeckeThetaData.complexGenericPointEquiv R.point

def Data.ActiveHeckeThetaData.ReferencePELPointData.genericFamilyIso :
    AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso (D.pel.fiberFamily (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint) R.genericPoint) R.family :=
  (Data.ActiveHeckeThetaData.complexGenericFamilyIso R.point).trans R.point_family.some

end

end OAI.RepresentationTheory.Theta.Geometric
