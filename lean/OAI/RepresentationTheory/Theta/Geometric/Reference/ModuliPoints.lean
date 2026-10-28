import OAI.RepresentationTheory.Theta.Geometric.Reference.PELCompatibility
import OAI.RepresentationTheory.Theta.Geometric.Complex.PELClassification
import OAI.RepresentationTheory.Theta.Geometric.Reference.ModelTransport

/-! # Moduli Points -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Each original ball point gives an actual polarized reference family
and its unique classifying point in TateComparison's original complex moduli fiber. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (x : D.domain)

structure Data.ActiveHeckeThetaData.ReferencePELPointData where
  model : D.PeriodModel hg x
  analytic : D.ReferenceAnalyticFiber x
  dual : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel (analytic.toNativeReference D) hg.reference_admissible
  isogeny : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.ReferenceLatticeIsogeny (model.toNativeReferenceModel analytic) dual
  polarization : Reference.PolarizationConstruction.ReferencePolarizationConstruction isogeny

theorem Data.ActiveHeckeThetaData.referencePELPointData_nonempty : Nonempty (D.ReferencePELPointData hg x) := by
  let M := D.periodModel hg x
  let F := D.referenceAnalyticFiber hg x
  let N := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.referenceDualModel (F.toNativeReference D) hg.reference_admissible
  let p := Classical.choice (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel.referenceLatticeIsogeny_nonempty (M.toNativeReferenceModel F) N)
  exact ⟨⟨M, F, N, p, Classical.choice (Reference.PolarizationConstruction.referencePolarizationConstruction_nonempty p)⟩⟩

def Data.ActiveHeckeThetaData.referencePELPointData : D.ReferencePELPointData hg x :=
  Classical.choice (D.referencePELPointData_nonempty hg x)

section

variable {D hg x} (R : D.ReferencePELPointData hg x)

def Data.ActiveHeckeThetaData.ReferencePELPointData.family : AlgebraicGeometry.AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.pel.level AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase :=
  letI : NeZero D.pel.level := ⟨by have h := hg.fullLevel; omega⟩
  R.polarization.pelFamily D.pel.level

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.family_isPEL : AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.IsPELFamily D.pel.reference (Reference.LieSignature.referenceComplexBaseAction D.pel.reference) R.family := by
  let : NeZero D.pel.level := ⟨by have h := hg.fullLevel; omega⟩
  exact R.polarization.pelFamily_isPEL D.pel.level

def Data.ActiveHeckeThetaData.ReferencePELPointData.point : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace :=
  (Complex.PELClassification.existsUnique_complexPELPoint D.pel hg R.family R.family_isPEL).choose

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.point_family :
    Nonempty (AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso (D.pel.model.family.pullback (Complex.PELClassification.modelComplexPointEquiv D.pel R.point).left) R.family) :=
  (Complex.PELClassification.existsUnique_complexPELPoint D.pel hg R.family R.family_isPEL).choose_spec.1

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.point_unique (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace)
    (hy : Nonempty (AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso (D.pel.model.family.pullback (Complex.PELClassification.modelComplexPointEquiv D.pel y).left) R.family)) :
    y = R.point :=
  (Complex.PELClassification.existsUnique_complexPELPoint D.pel hg R.family R.family_isPEL).choose_spec.2 y hy

end

def Data.ActiveHeckeThetaData.referenceModuliMap : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace :=
  fun z => (D.referencePELPointData hg z).point

theorem Data.ActiveHeckeThetaData.referenceModuliMap_family (z : D.domain) :
    Nonempty (AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso
      (D.pel.model.family.pullback (Complex.PELClassification.modelComplexPointEquiv D.pel (D.referenceModuliMap hg z)).left)
      (D.referencePELPointData hg z).family) :=
  (D.referencePELPointData hg z).point_family

end

end OAI.RepresentationTheory.Theta.Geometric
