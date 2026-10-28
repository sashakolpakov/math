import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicConnection
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ConnectionPullbackChange
import OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ConnectionTransgression

/-! # Connection Theta Cech -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

section

/-! The constructed native frame connections and logarithms, normalized
in the same genuine Cech complex as the original rational Chern class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence
open scoped _root_.Manifold ContDiff

def ConnectionThetaCech.Geometric.chernLogScale : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹

theorem ConnectionThetaCech.Geometric.neg_chernLogScale : -ConnectionThetaCech.Geometric.chernLogScale = Complex.I / (2 * (Real.pi : ℂ)) := by
  unfold ConnectionThetaCech.Geometric.chernLogScale
  field_simp
  simp [Complex.I_sq]

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim} {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix} {hP : matrix.transpose = -matrix}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel F) (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family ((PolarizationFactor.Geometric.polarizationFactor F) hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))

local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaCech_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaCech_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaChernIntersection_subset {n : ℕ}
    (a : Fin (n + 1) → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (k : Fin (n + 1)) :
    AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a ≤
      AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ChernFrames.Geometric.thetaLocalLineFrame f.left g.left (a k).2) :=
  (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a k).trans ((M.thetaChernLogRefinement U V f g hf hg).subset (a k))

theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaChernLogCech_holomorphic
    (a : Fin 2 → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    ContMDiff 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) 𝓘(ℂ, ℂ) ∞ (M.thetaChernLogCech U V f g hf hg a) :=
  (M.thetaChernLogRefinement_holomorphic U V f g hf hg (a 0) (a 1)).comp
    (contMDiff_inclusion (I := 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)) (n := ∞)
      (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 1)))

def PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaConnectionOnIntersection (hdeg : V.degree = U.degree + 1) {n : ℕ}
    (a : Fin (n + 1) → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (k : Fin (n + 1)) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) 1 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (M.thetaChernIntersection_subset U V f g hf hg a k)
    (M.nativeThetaConnection U V f g hf hg hdeg (a k).2)

def PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaConnectionCech (hdeg : V.degree = U.degree + 1) :
    Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (M.thetaChernCover U V f g hf hg) 1 0 :=
  fun a => -ConnectionThetaCech.Geometric.chernLogScale • M.nativeThetaConnectionOnIntersection U V f g hf hg hdeg a 0

def PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaLogarithmCech :
    Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (M.thetaChernCover U V f g hf hg) 0 1 :=
  fun a => (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) _ 0).symm
    (ConnectionThetaCech.Geometric.chernLogScale • ComplexMultiplication.HodgeComparison.SmoothScalarConstruction.CM.Construction.scalarManifoldForm (M.thetaChernLogCech U V f g hf hg a)
      (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex (M.thetaChernLogCech_holomorphic U V f g hf hg a)))

def PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaNormalizedCurvature :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) 2 :=
  -ConnectionThetaCech.Geometric.chernLogScale • M.nativeReferenceCurvature

theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaConnectionCech_d (hdeg : V.degree = U.degree + 1) :
    Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechExteriorD (M.thetaChernCover U V f g hf hg) 1 0
        (M.nativeThetaConnectionCech U V f g hf hg hdeg) =
      Analysis.DifferentialForms.Manifold.CechAugmentation.manifoldCechAugmentation (M.thetaChernCover U V f g hf hg) 2 M.nativeThetaNormalizedCurvature := by
  funext a
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (-ConnectionThetaCech.Geometric.chernLogScale • Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict
    (M.thetaChernIntersection_subset U V f g hf hg a 0)
    (M.nativeThetaConnection U V f g hf hg hdeg (a 0).2)) = _
  rw [map_smul, ← Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_d, M.nativeThetaConnection_curvature,
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.restrict_onOpen]
  rfl

end

section

/-! The original Chern logarithms have the exact theta ratio at every
period lift of every point of their Cech intersection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence
open scoped _root_.Manifold ContDiff

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim} {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix} {hP : matrix.transpose = -matrix}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel F) (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family ((PolarizationFactor.Geometric.polarizationFactor F) hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))

local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaCechPeriods_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaCechPeriods_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

def PeriodModel.Geometric.AlgebraicPeriodModel.thetaIntersectionPeriod {n : ℕ}
    (a : Fin (n + 1) → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a → (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus :=
  fun p => M.period.symm p.val

theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaIntersectionPeriod_holomorphic {n : ℕ}
    (a : Fin (n + 1) → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    ContMDiff 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) 𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData F).space) ∞
      (M.thetaIntersectionPeriod U V f g hf hg a) :=
  M.period.symm.contMDiff.comp (contMDiff_subtype_val (I := 𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)) (n := ∞))

theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaIntersectionPeriod_domain {n : ℕ}
    (a : Fin (n + 1) → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (k : Fin (n + 1))
    (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) :
    M.thetaIntersectionPeriod U V f g hf hg a p ∈ (TorusTheta.Geometric.thetaTorusFrameOpen F) hP U V (a k).2 :=
  M.thetaNativeFrame_period_inverse U V f g hf hg (a k).2
    (M.thetaChernIntersection_subset U V f g hf hg a k p.property)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaChernLogCech_period_exp
    (a : Fin 2 → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) (w : (ProjectivePeriodData.Geometric.projectivePeriodData F).space)
    (hw : (QuotientAddGroup.mk w : (ProjectivePeriodData.Geometric.projectivePeriodData F).periodTorus) = M.thetaIntersectionPeriod U V f g hf hg a p) :
    Complex.exp (M.thetaChernLogCech U V f g hf hg a p) =
      RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V (a 1).2.1 (a 1).2.2 w / RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V (a 0).2.1 (a 0).2.2 w := by
  have hp : M.vectorPeriod w = p.val :=
    (congrArg M.period hw).trans (M.period.apply_symm_apply p.val)
  have hm (k : Fin 2) : w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V (a k).2 := by
    apply (M.thetaFrameOpen_period U V f g hf hg (a k).2 w).mp
    exact (congrArg (fun q => q.left (default : Foundations.Scheme.ProjectiveSpace.complexBase) ∈
      RepresentationTheory.Theta.Geometric.ProductFrames.thetaQuotientOpen f.left g.left (a k).2.1 (a k).2.2) hp).mpr
        (M.thetaChernIntersection_subset U V f g hf hg a k p.property)
  let r := ChernFrames.Geometric.thetaLocalLineFrame f.left g.left (a 0).2
  let t := ChernFrames.Geometric.thetaLocalLineFrame f.left g.left (a 1).2
  let D := AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation r ⊓
    AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation t
  have he : (⟨M.vectorPeriod w,
      (M.thetaFrameOpen_period U V f g hf hg (a 0).2 w).mpr (hm 0),
      (M.thetaFrameOpen_period U V f g hf hg (a 1).2 w).mpr (hm 1)⟩ : D) =
      ⟨p.val, M.thetaChernIntersection_subset U V f g hf hg a 0 p.property,
        M.thetaChernIntersection_subset U V f g hf hg a 1 p.property⟩ := Subtype.ext hp
  exact (M.thetaChernLogCech_exp U V f g hf hg a p).trans
    ((congrArg (AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameTransitionPair M.abelian.variety.presentation r t) he).symm.trans
      (M.thetaLocalLineFrame_period_transition U V f g hf hg (a 0).2 (a 1).2 w (hm 0) (hm 1)))

theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaConnectionOnIntersection_intrinsic (hdeg : V.degree = U.degree + 1) {n : ℕ}
    (a : Fin (n + 1) → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (k : Fin (n + 1)) :
    (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) _ 1
      (M.nativeThetaConnectionOnIntersection U V f g hf hg hdeg a k)).val =
        ((TorusTheta.Geometric.thetaTorusConnectionRaw F) hP U V (a k).2).pullback (M.thetaIntersectionPeriod U V f g hf hg a) := by
  funext p
  exact (congrFun (((TorusTheta.Geometric.thetaTorusConnectionRaw F) hP U V (a k).2).pullback_comp
    (Subtype.val : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    ((contMDiff_subtype_val (I := 𝓘(ℝ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)) (n := ∞)).mdifferentiable (by simp))
    M.period.symm ((Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex M.period.symm.contMDiff).mdifferentiable (by simp))) p).symm

end

/-! The native connection changes by the differential of its constructed
Chern logarithm. The actual signed Cech-de Rham differential therefore
expresses curvature minus logarithmic defect as a boundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence
open scoped _root_.Manifold ContDiff

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim} {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix} {hP : matrix.transpose = -matrix}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel F) (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family ((PolarizationFactor.Geometric.polarizationFactor F) hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))

local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaCechTransition_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaCechTransition_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

def PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaLogPrimitive
    (a : Fin 2 → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) 0 :=
  (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) 0).symm
    (ComplexMultiplication.HodgeComparison.SmoothScalarConstruction.CM.Construction.scalarManifoldForm (M.thetaChernLogCech U V f g hf hg a)
      (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex (M.thetaChernLogCech_holomorphic U V f g hf hg a)))

theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaLogarithmCech_scale
    (a : Fin 2 → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    M.nativeThetaLogarithmCech U V f g hf hg a = ConnectionThetaCech.Geometric.chernLogScale • M.nativeThetaLogPrimitive U V f g hf hg a :=
  (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) 0).symm.map_smul ConnectionThetaCech.Geometric.chernLogScale _

theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaConnectionOnIntersection_change (hdeg : V.degree = U.degree + 1)
    (a : Fin 2 → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    M.nativeThetaConnectionOnIntersection U V f g hf hg hdeg a 1 -
      M.nativeThetaConnectionOnIntersection U V f g hf hg hdeg a 0 =
        Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (M.nativeThetaLogPrimitive U V f g hf hg a) := by
  apply (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) 1).injective
  refine ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) 1).map_sub
    (M.nativeThetaConnectionOnIntersection U V f g hf hg hdeg a 1)
    (M.nativeThetaConnectionOnIntersection U V f g hf hg hdeg a 0)).trans ?_
  let b := ComplexMultiplication.HodgeComparison.SmoothScalarConstruction.CM.Construction.scalarManifoldForm (M.thetaChernLogCech U V f g hf hg a)
    (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex (M.thetaChernLogCech_holomorphic U V f g hf hg a))
  have hd : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b = (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) 1)
      (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (M.nativeThetaLogPrimitive U V f g hf hg a)) :=
    (congrArg Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d
      ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) 0).apply_symm_apply b)).symm.trans
        (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_d (M.nativeThetaLogPrimitive U V f g hf hg a))
  refine Eq.trans ?_ hd
  apply Subtype.ext
  have h := (ConnectionPullbackChange.Geometric.thetaTorusConnection_pullback_logarithmic_change F) hP U V hdeg (a 0).2 (a 1).2
    (M.thetaIntersectionPeriod U V f g hf hg a) (M.thetaChernLogCech U V f g hf hg a)
    (M.thetaIntersectionPeriod_holomorphic U V f g hf hg a)
    (M.thetaChernLogCech_holomorphic U V f g hf hg a)
    (M.thetaIntersectionPeriod_domain U V f g hf hg a 0)
    (M.thetaIntersectionPeriod_domain U V f g hf hg a 1)
    (M.thetaChernLogCech_period_exp U V f g hf hg a)
  exact (congrArg₂ (fun b c : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) 1 => b - c)
    (M.nativeThetaConnectionOnIntersection_intrinsic U V f g hf hg hdeg a 1)
    (M.nativeThetaConnectionOnIntersection_intrinsic U V f g hf hg hdeg a 0)).trans h

theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaConnectionCech_delta_apply (hdeg : V.degree = U.degree + 1)
    (a : Fin 2 → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta (M.thetaChernCover U V f g hf hg) 1 0
        (M.nativeThetaConnectionCech U V f g hf hg hdeg) a =
      -ConnectionThetaCech.Geometric.chernLogScale • M.nativeThetaConnectionOnIntersection U V f g hf hg hdeg a 1 -
        -ConnectionThetaCech.Geometric.chernLogScale • M.nativeThetaConnectionOnIntersection U V f g hf hg hdeg a 0 := by
  have h := AlgebraicTopology.DeRham.Comparison.SmoothCech.cechDelta_apply (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) 1) (M.thetaChernCover U V f g hf hg)
    0 (M.nativeThetaConnectionCech U V f g hf hg hdeg) a
  refine h.trans ?_
  rw [Fin.sum_univ_two]
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro p
  ext v
  change (1 : ℤ) • (-ConnectionThetaCech.Geometric.chernLogScale * (M.nativeThetaConnectionRaw U V (a 1).2 p.val v)) +
    (-1 : ℤ) • (-ConnectionThetaCech.Geometric.chernLogScale * (M.nativeThetaConnectionRaw U V (a 0).2 p.val v)) = _
  simp only [one_smul, neg_one_smul]
  rfl

theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaConnectionCech_delta (hdeg : V.degree = U.degree + 1) :
    Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta (M.thetaChernCover U V f g hf hg) 1 0
        (M.nativeThetaConnectionCech U V f g hf hg hdeg) =
      -Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechExteriorD (M.thetaChernCover U V f g hf hg) 0 1
        (M.nativeThetaLogarithmCech U V f g hf hg) := by
  funext a
  refine (M.nativeThetaConnectionCech_delta_apply U V f g hf hg hdeg a).trans ?_
  refine (smul_sub (-ConnectionThetaCech.Geometric.chernLogScale)
    (M.nativeThetaConnectionOnIntersection U V f g hf hg hdeg a 1)
    (M.nativeThetaConnectionOnIntersection U V f g hf hg hdeg a 0)).symm.trans ?_
  refine (congrArg (fun b => -ConnectionThetaCech.Geometric.chernLogScale • b)
    (M.nativeThetaConnectionOnIntersection_change U V f g hf hg hdeg a)).trans ?_
  change _ = -Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (M.nativeThetaLogarithmCech U V f g hf hg a)
  have hd := (congrArg Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (M.nativeThetaLogarithmCech_scale U V f g hf hg a)).trans
    (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d.map_smul ConnectionThetaCech.Geometric.chernLogScale (M.nativeThetaLogPrimitive U V f g hf hg a))
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro p
  ext v
  have hv := congrArg (fun b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) 1 => b p v) hd
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (M.nativeThetaLogarithmCech U V f g hf hg a) p v =
    ConnectionThetaCech.Geometric.chernLogScale * Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (M.nativeThetaLogPrimitive U V f g hf hg a) p v at hv
  change -ConnectionThetaCech.Geometric.chernLogScale * Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (M.nativeThetaLogPrimitive U V f g hf hg a) p v =
    -(Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (M.nativeThetaLogarithmCech U V f g hf hg a) p v)
  rw [hv, neg_mul]

theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativeTheta_curvature_logarithmic_boundary (hdeg : V.degree = U.degree + 1) :
    (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (M.thetaChernCover U V f g hf hg)).d 1 2
      (ComplexMultiplication.HodgeComparison.ConnectionTransgression.CM.Construction.connectionTotalPrimitive (M.thetaChernCover U V f g hf hg)
        (M.nativeThetaConnectionCech U V f g hf hg hdeg) (M.nativeThetaLogarithmCech U V f g hf hg)) =
      (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechAugmentationToTotal (E := HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (M.thetaChernCover U V f g hf hg)).f 2
        M.nativeThetaNormalizedCurvature -
      Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion (M.thetaChernCover U V f g hf hg) 2 0 2 rfl
        (Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta (M.thetaChernCover U V f g hf hg) 0 1 (M.nativeThetaLogarithmCech U V f g hf hg)) :=
  ComplexMultiplication.HodgeComparison.ConnectionTransgression.CM.Construction.connection_curvature_total_boundary (M.thetaChernCover U V f g hf hg)
    M.nativeThetaNormalizedCurvature (M.nativeThetaConnectionCech U V f g hf hg hdeg)
    (M.nativeThetaLogarithmCech U V f g hf hg) (M.nativeThetaConnectionCech_d U V f g hf hg hdeg)
    (M.nativeThetaConnectionCech_delta U V f g hf hg hdeg)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
