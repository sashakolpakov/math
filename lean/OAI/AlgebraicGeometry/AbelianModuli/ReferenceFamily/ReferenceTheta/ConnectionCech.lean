import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.ThetaConnection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.ConnectionPullbackChange
import OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ConnectionTransgression

/-! # Connection Cech -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

section

/-! The constructed native frame connections and logarithms, normalized
in the same genuine Cech complex as the original rational Chern class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence
open scoped _root_.Manifold ContDiff

def ReferenceTheta.ConnectionCech.chernLogScale : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹

theorem ReferenceTheta.ConnectionCech.neg_chernLogScale : -ReferenceTheta.ConnectionCech.chernLogScale = Complex.I / (2 * (Real.pi : ℂ)) := by
  unfold ReferenceTheta.ConnectionCech.chernLogScale
  field_simp
  simp [Complex.I_sq]

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP) (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaCech_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaCech_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaChernIntersection_subset {n : ℕ}
    (a : Fin (n + 1) → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (k : Fin (n + 1)) :
    AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a ≤
      AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation (ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left (a k).2) :=
  (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a k).trans ((M.thetaChernLogRefinement U V f g hf hg).subset (a k))

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaChernLogCech_holomorphic
    (a : Fin 2 → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    ContMDiff 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) 𝓘(ℂ, ℂ) ∞ (M.thetaChernLogCech U V f g hf hg a) :=
  (M.thetaChernLogRefinement_holomorphic U V f g hf hg (a 0) (a 1)).comp
    (contMDiff_inclusion (I := 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)) (n := ∞)
      (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 1)))

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaConnectionOnIntersection (hdeg : V.degree = U.degree + 1) {n : ℕ}
    (a : Fin (n + 1) → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (k : Fin (n + 1)) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) 1 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (M.thetaChernIntersection_subset U V f g hf hg a k)
    (M.nativeThetaConnection U V f g hf hg hdeg (a k).2)

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaConnectionCech (hdeg : V.degree = U.degree + 1) :
    Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M.thetaChernCover U V f g hf hg) 1 0 :=
  fun a => -ReferenceTheta.ConnectionCech.chernLogScale • M.nativeThetaConnectionOnIntersection U V f g hf hg hdeg a 0

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaLogarithmCech :
    Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M.thetaChernCover U V f g hf hg) 0 1 :=
  fun a => (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) _ 0).symm
    (ReferenceTheta.ConnectionCech.chernLogScale • ComplexMultiplication.HodgeComparison.SmoothScalarConstruction.CM.Construction.scalarManifoldForm (M.thetaChernLogCech U V f g hf hg a)
      (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex (M.thetaChernLogCech_holomorphic U V f g hf hg a)))

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaNormalizedCurvature :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) 2 :=
  -ReferenceTheta.ConnectionCech.chernLogScale • M.nativeReferenceCurvature

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaConnectionCech_d (hdeg : V.degree = U.degree + 1) :
    Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechExteriorD (M.thetaChernCover U V f g hf hg) 1 0
        (M.nativeThetaConnectionCech U V f g hf hg hdeg) =
      Analysis.DifferentialForms.Manifold.CechAugmentation.manifoldCechAugmentation (M.thetaChernCover U V f g hf hg) 2 M.nativeThetaNormalizedCurvature := by
  funext a
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (-ReferenceTheta.ConnectionCech.chernLogScale • Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict
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

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP) (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaCechPeriods_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaCechPeriods_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

def Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaIntersectionPeriod {n : ℕ}
    (a : Fin (n + 1) → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a → F.periodData.periodTorus :=
  fun p => M.period.symm p.val

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaIntersectionPeriod_holomorphic {n : ℕ}
    (a : Fin (n + 1) → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    ContMDiff 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) 𝓘(ℂ, F.periodData.space) ∞
      (M.thetaIntersectionPeriod U V f g hf hg a) :=
  M.period.symm.contMDiff.comp (contMDiff_subtype_val (I := 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)) (n := ∞))

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaIntersectionPeriod_domain {n : ℕ}
    (a : Fin (n + 1) → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (k : Fin (n + 1))
    (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) :
    M.thetaIntersectionPeriod U V f g hf hg a p ∈ F.thetaTorusFrameOpen hP U V (a k).2 :=
  M.thetaNativeFrame_period_inverse U V f g hf hg (a k).2
    (M.thetaChernIntersection_subset U V f g hf hg a k p.property)

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaChernLogCech_period_exp
    (a : Fin 2 → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension)
    (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) (w : F.periodData.space)
    (hw : (QuotientAddGroup.mk w : F.periodData.periodTorus) = M.thetaIntersectionPeriod U V f g hf hg a p) :
    Complex.exp (M.thetaChernLogCech U V f g hf hg a p) =
      RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V (a 1).2.1 (a 1).2.2 w / RepresentationTheory.Theta.Geometric.ConsecutiveGauge.CM.Torus.AutomorphicTheta.consecutiveGauge U V (a 0).2.1 (a 0).2.2 w := by
  have hp : M.vectorPeriod w = p.val :=
    (congrArg M.period hw).trans (M.period.apply_symm_apply p.val)
  have hm (k : Fin 2) : w ∈ RepresentationTheory.Theta.Geometric.GaugeOpens.thetaGaugeOpen U V (a k).2 := by
    apply (M.thetaFrameOpen_period U V f g hf hg (a k).2 w).mp
    exact (congrArg (fun q => q.left (default : Foundations.Scheme.ProjectiveSpace.complexBase) ∈
      RepresentationTheory.Theta.Geometric.ProductFrames.thetaQuotientOpen f.left g.left (a k).2.1 (a k).2.2) hp).mpr
        (M.thetaChernIntersection_subset U V f g hf hg a k p.property)
  let r := ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left (a 0).2
  let t := ReferenceTheta.ChernFrames.thetaLocalLineFrame f.left g.left (a 1).2
  let D := AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation r ⊓
    AnalyticFrameTransitions.frameAnalyticOpen M.abelian.variety.presentation t
  have he : (⟨M.vectorPeriod w,
      (M.thetaFrameOpen_period U V f g hf hg (a 0).2 w).mpr (hm 0),
      (M.thetaFrameOpen_period U V f g hf hg (a 1).2 w).mpr (hm 1)⟩ : D) =
      ⟨p.val, M.thetaChernIntersection_subset U V f g hf hg a 0 p.property,
        M.thetaChernIntersection_subset U V f g hf hg a 1 p.property⟩ := Subtype.ext hp
  exact (M.thetaChernLogCech_exp U V f g hf hg a p).trans
    ((congrArg (AnalyticFrameTransitions.frameTransitionPair M.abelian.variety.presentation r t) he).symm.trans
      (M.thetaLocalLineFrame_period_transition U V f g hf hg (a 0).2 (a 1).2 w (hm 0) (hm 1)))

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaConnectionOnIntersection_intrinsic (hdeg : V.degree = U.degree + 1) {n : ℕ}
    (a : Fin (n + 1) → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) (k : Fin (n + 1)) :
    (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) _ 1
      (M.nativeThetaConnectionOnIntersection U V f g hf hg hdeg a k)).val =
        (F.thetaTorusConnectionRaw hP U V (a k).2).pullback (M.thetaIntersectionPeriod U V f g hf hg a) := by
  funext p
  exact (congrFun ((F.thetaTorusConnectionRaw hP U V (a k).2).pullback_comp
    (Subtype.val : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
    ((contMDiff_subtype_val (I := 𝓘(ℝ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)) (n := ∞)).mdifferentiable (by simp))
    M.period.symm ((Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex M.period.symm.contMDiff).mdifferentiable (by simp))) p).symm

end

/-! The native connection changes by the differential of its constructed
Chern logarithm. The actual signed Cech-de Rham differential therefore
expresses curvature minus logarithmic defect as a boundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence
open scoped _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP) (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaCechTransition_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaCechTransition_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaLogPrimitive
    (a : Fin 2 → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) 0 :=
  (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) 0).symm
    (ComplexMultiplication.HodgeComparison.SmoothScalarConstruction.CM.Construction.scalarManifoldForm (M.thetaChernLogCech U V f g hf hg a)
      (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex (M.thetaChernLogCech_holomorphic U V f g hf hg a)))

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaLogarithmCech_scale
    (a : Fin 2 → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    M.nativeThetaLogarithmCech U V f g hf hg a = ReferenceTheta.ConnectionCech.chernLogScale • M.nativeThetaLogPrimitive U V f g hf hg a :=
  (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) 0).symm.map_smul ReferenceTheta.ConnectionCech.chernLogScale _

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaConnectionOnIntersection_change (hdeg : V.degree = U.degree + 1)
    (a : Fin 2 → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    M.nativeThetaConnectionOnIntersection U V f g hf hg hdeg a 1 -
      M.nativeThetaConnectionOnIntersection U V f g hf hg hdeg a 0 =
        Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (M.nativeThetaLogPrimitive U V f g hf hg a) := by
  apply (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) 1).injective
  refine ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) 1).map_sub
    (M.nativeThetaConnectionOnIntersection U V f g hf hg hdeg a 1)
    (M.nativeThetaConnectionOnIntersection U V f g hf hg hdeg a 0)).trans ?_
  let b := ComplexMultiplication.HodgeComparison.SmoothScalarConstruction.CM.Construction.scalarManifoldForm (M.thetaChernLogCech U V f g hf hg a)
    (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex (M.thetaChernLogCech_holomorphic U V f g hf hg a))
  have hd : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b = (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) 1)
      (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (M.nativeThetaLogPrimitive U V f g hf hg a)) :=
    (congrArg Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d
      ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) 0).apply_symm_apply b)).symm.trans
        (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_d (M.nativeThetaLogPrimitive U V f g hf hg a))
  refine Eq.trans ?_ hd
  apply Subtype.ext
  have h := F.thetaTorusConnection_pullback_logarithmic_change hP U V hdeg (a 0).2 (a 1).2
    (M.thetaIntersectionPeriod U V f g hf hg a) (M.thetaChernLogCech U V f g hf hg a)
    (M.thetaIntersectionPeriod_holomorphic U V f g hf hg a)
    (M.thetaChernLogCech_holomorphic U V f g hf hg a)
    (M.thetaIntersectionPeriod_domain U V f g hf hg a 0)
    (M.thetaIntersectionPeriod_domain U V f g hf hg a 1)
    (M.thetaChernLogCech_period_exp U V f g hf hg a)
  exact (congrArg₂ (fun b c : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) 1 => b - c)
    (M.nativeThetaConnectionOnIntersection_intrinsic U V f g hf hg hdeg a 1)
    (M.nativeThetaConnectionOnIntersection_intrinsic U V f g hf hg hdeg a 0)).trans h

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaConnectionCech_delta_apply (hdeg : V.degree = U.degree + 1)
    (a : Fin 2 → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver ×
      RepresentationTheory.Theta.Geometric.QuotientIndexedFrames.ThetaFrameIndex U.projectiveDimension V.projectiveDimension) :
    Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta (M.thetaChernCover U V f g hf hg) 1 0
        (M.nativeThetaConnectionCech U V f g hf hg hdeg) a =
      -ReferenceTheta.ConnectionCech.chernLogScale • M.nativeThetaConnectionOnIntersection U V f g hf hg hdeg a 1 -
        -ReferenceTheta.ConnectionCech.chernLogScale • M.nativeThetaConnectionOnIntersection U V f g hf hg hdeg a 0 := by
  have h := AlgebraicTopology.DeRham.Comparison.SmoothCech.cechDelta_apply (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) 1) (M.thetaChernCover U V f g hf hg)
    0 (M.nativeThetaConnectionCech U V f g hf hg hdeg) a
  refine h.trans ?_
  rw [Fin.sum_univ_two]
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro p
  ext v
  change (1 : ℤ) • (-ReferenceTheta.ConnectionCech.chernLogScale * (M.nativeThetaConnectionRaw U V (a 1).2 p.val v)) +
    (-1 : ℤ) • (-ReferenceTheta.ConnectionCech.chernLogScale * (M.nativeThetaConnectionRaw U V (a 0).2 p.val v)) = _
  simp only [one_smul, neg_one_smul]
  rfl

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaConnectionCech_delta (hdeg : V.degree = U.degree + 1) :
    Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta (M.thetaChernCover U V f g hf hg) 1 0
        (M.nativeThetaConnectionCech U V f g hf hg hdeg) =
      -Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechExteriorD (M.thetaChernCover U V f g hf hg) 0 1
        (M.nativeThetaLogarithmCech U V f g hf hg) := by
  funext a
  refine (M.nativeThetaConnectionCech_delta_apply U V f g hf hg hdeg a).trans ?_
  refine (smul_sub (-ReferenceTheta.ConnectionCech.chernLogScale)
    (M.nativeThetaConnectionOnIntersection U V f g hf hg hdeg a 1)
    (M.nativeThetaConnectionOnIntersection U V f g hf hg hdeg a 0)).symm.trans ?_
  refine (congrArg (fun b => -ReferenceTheta.ConnectionCech.chernLogScale • b)
    (M.nativeThetaConnectionOnIntersection_change U V f g hf hg hdeg a)).trans ?_
  change _ = -Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (M.nativeThetaLogarithmCech U V f g hf hg a)
  have hd := (congrArg Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (M.nativeThetaLogarithmCech_scale U V f g hf hg a)).trans
    (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d.map_smul ReferenceTheta.ConnectionCech.chernLogScale (M.nativeThetaLogPrimitive U V f g hf hg a))
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro p
  ext v
  have hv := congrArg (fun b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (M.thetaChernCover U V f g hf hg) a) 1 => b p v) hd
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (M.nativeThetaLogarithmCech U V f g hf hg a) p v =
    ReferenceTheta.ConnectionCech.chernLogScale * Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (M.nativeThetaLogPrimitive U V f g hf hg a) p v at hv
  change -ReferenceTheta.ConnectionCech.chernLogScale * Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (M.nativeThetaLogPrimitive U V f g hf hg a) p v =
    -(Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (M.nativeThetaLogarithmCech U V f g hf hg a) p v)
  rw [hv, neg_mul]

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeTheta_curvature_logarithmic_boundary (hdeg : V.degree = U.degree + 1) :
    (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M.thetaChernCover U V f g hf hg)).d 1 2
      (ComplexMultiplication.HodgeComparison.ConnectionTransgression.CM.Construction.connectionTotalPrimitive (M.thetaChernCover U V f g hf hg)
        (M.nativeThetaConnectionCech U V f g hf hg hdeg) (M.nativeThetaLogarithmCech U V f g hf hg)) =
      (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechAugmentationToTotal (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M.thetaChernCover U V f g hf hg)).f 2
        M.nativeThetaNormalizedCurvature -
      Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion (M.thetaChernCover U V f g hf hg) 2 0 2 rfl
        (Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta (M.thetaChernCover U V f g hf hg) 0 1 (M.nativeThetaLogarithmCech U V f g hf hg)) :=
  ComplexMultiplication.HodgeComparison.ConnectionTransgression.CM.Construction.connection_curvature_total_boundary (M.thetaChernCover U V f g hf hg)
    M.nativeThetaNormalizedCurvature (M.nativeThetaConnectionCech U V f g hf hg hdeg)
    (M.nativeThetaLogarithmCech U V f g hf hg) (M.nativeThetaConnectionCech_d U V f g hf hg hdeg)
    (M.nativeThetaConnectionCech_delta U V f g hf hg hdeg)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
