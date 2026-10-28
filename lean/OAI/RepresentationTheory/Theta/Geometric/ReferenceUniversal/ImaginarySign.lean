import OAI.RepresentationTheory.Theta.Geometric.Reference.FieldMarkingBall
import OAI.RepresentationTheory.Theta.Geometric.ReferenceUniversal.Polarization
import OAI.RepresentationTheory.Theta.Geometric.ReferenceUniversal.MarkingKernel

/-! # Imaginary Sign -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The actual original reference PEL fiber fixes the positive
distinguished imaginary sign of the precisely scaled trace coefficient. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.universalFiberIso Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {a : D.domain} (R : D.ReferencePELPointData hg a)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsReduced S.left] (f : S ⟶ D.pel.complexSpace)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (hx : x ≫ f = R.point)

include hx in
theorem Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversal_referenceImaginary_positive (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    0 < ((D.pel.reference.embeddings D.pel.reference.distinguished) (Reference.DiagonalHermitian.referenceTraceScalar D.pel.reference)).im := by
  apply Reference.FieldMarkingBall.fieldMarking_referenceImaginary_positive (Universal.PELConditions.complexUniversalPolarized D.pel hg f)
    (Universal.PELConditions.complexUniversalAction D.pel hg f) x s hs rfl hdegree (R.nativeUniversalFieldMarking f x hx)
    (Universal.PELConditions.complexUniversal_rosati D.pel hg f) D.pel.reference hg.reference_admissible
    (fun v w => R.nativeUniversalRationalMarking_polarization f x hx v w)
    (D.referenceDomainPoint a)
  exact R.nativeUniversalFieldMarking_kernel f x hx

end

end OAI.RepresentationTheory.Theta.Geometric
