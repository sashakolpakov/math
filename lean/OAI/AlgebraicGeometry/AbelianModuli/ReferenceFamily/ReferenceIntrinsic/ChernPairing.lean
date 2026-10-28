import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.CurvatureInvariant
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.PeriodDifferential
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.Marking
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPeriod

/-! # Chern Pairing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The original native Chern pairing, evaluated on the actual reference
period marking, is exactly the prescribed original integral form. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeChernPairing_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeChernPairing_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaClosedForm_period (u v : F.periodData.space) :
    M.nativeThetaClosedForm.val 1 ![M.periodDifferential u, M.periodDifferential v] =
      (Complex.I / (2 * (Real.pi : ℂ))) * F.referenceCurvature 0 ![u, v] := by
  let q := M.period.symm (1 : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
  let D : RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian →L[ℝ] F.periodData.space :=
    mfderiv 𝓘(ℝ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) 𝓘(ℝ, F.periodData.space) M.period.symm 1
  have ht (w : F.periodData.space) :
      Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (F.periodData.periodChart q) q (D (M.periodDifferential w)) = w :=
    (Holomorphic.TangentMaps.preferredTangent_identity (E := F.periodData.space) (M := F.periodData.periodTorus)
      q (D (M.periodDifferential w))).trans (M.inversePeriodRealDifferential_apply w)
  change -ReferenceTheta.ConnectionCech.chernLogScale * RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationCurvature F.form (F.periodData.periodChart q q)
    (fun k => Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (F.periodData.periodChart q) q
      (D (![M.periodDifferential u, M.periodDifferential v] k))) = _
  have hv : (fun k => Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (F.periodData.periodChart q) q
      (D (![M.periodDifferential u, M.periodDifferential v] k))) = ![u, v] := by
    funext k
    fin_cases k
    · exact ht u
    · exact ht v
  rw [hv, ReferenceTheta.ConnectionCech.neg_chernLogScale]
  change _ = (Complex.I / (2 * (Real.pi : ℂ))) * RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationCurvature F.form 0 ![u, v]
  exact congrArg (fun b : ℂ => (Complex.I / (2 * (Real.pi : ℂ))) * b)
    ((RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationCurvature_apply F.form (F.periodData.periodChart q q) ![u, v]).trans
      (RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationCurvature_apply F.form 0 ![u, v]).symm)

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaChernCovector_integral
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))
    (hdeg : V.degree = U.degree + 1) (l m : P.lattice) :
    AmpleChernInvariant.nativeChernCovector M.abelian (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)
      ![(M.nativeReferenceMarking l.val).val, (M.nativeReferenceMarking m.val).val] =
      (P.integralForm l m : ℂ) := by
  have hc := congrArg (fun a : Analysis.DifferentialForms.Manifold.Basic.FormValue (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) 2 =>
    a ![(M.nativeReferenceMarking l.val).val, (M.nativeReferenceMarking m.val).val])
      (M.nativeThetaChernCovector_eq U V f g hf hg hdeg)
  exact hc.trans ((M.nativeThetaClosedForm_period (F.latticeEmbedding l) (F.latticeEmbedding m)).trans
    (F.referenceCurvature_integral hP l m 0))

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaChernForm_integral
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))
    (hdeg : V.degree = U.degree + 1) (l m : P.lattice) :
    Intrinsic.ChernPairing.nativeChernForm M.abelian (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)
      (M.nativeReferenceMarking l.val) (M.nativeReferenceMarking m.val) = (P.integralForm l m : ℚ) := by
  have h := (Intrinsic.ChernPeriod.nativeChernForm_covector M.abelian (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)
    (M.nativeReferenceMarking l.val) (M.nativeReferenceMarking m.val)).symm.trans
      (M.nativeThetaChernCovector_integral U V f g hf hg hdeg l m)
  exact_mod_cast h

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaChernForm_trace
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))
    (hdeg : V.degree = U.degree + 1) (u v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Intrinsic.ChernPairing.nativeChernForm M.abelian (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)
      (M.nativeReferenceMarking u) (M.nativeReferenceMarking v) = P.traceForm u v := by
  have hc := congrArg (fun a : Analysis.DifferentialForms.Manifold.Basic.FormValue (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) 2 =>
    a ![(M.nativeReferenceMarking u).val, (M.nativeReferenceMarking v).val])
      (M.nativeThetaChernCovector_eq U V f g hf hg hdeg)
  have hp := (M.nativeThetaClosedForm_period (F.periodEmbedding u) (F.periodEmbedding v)).trans
    (RepresentationTheory.Theta.Geometric.PolarizationCurvature.polarizationCurvature_normalized F.form F.hermitian 0 ![F.periodEmbedding u, F.periodEmbedding v])
  have htrace : ((F.form (F.periodEmbedding u) (F.periodEmbedding v)).im : ℂ) = (P.traceForm u v : ℂ) := by
    exact_mod_cast F.polarization u v
  have h := (Intrinsic.ChernPeriod.nativeChernForm_covector M.abelian (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)
    (M.nativeReferenceMarking u) (M.nativeReferenceMarking v)).symm.trans (hc.trans (hp.trans htrace))
  exact_mod_cast h

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.exists_ample_native_chern_pairing :
    ∃ L : HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left, L.IsAmple ∧
      (∀ l m : P.lattice, Intrinsic.ChernPairing.nativeChernForm M.abelian L
        (M.nativeReferenceMarking l.val) (M.nativeReferenceMarking m.val) = (P.integralForm l m : ℚ)) ∧
      (∀ u v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, Intrinsic.ChernPairing.nativeChernForm M.abelian L
        (M.nativeReferenceMarking u) (M.nativeReferenceMarking v) = P.traceForm u v) := by
  obtain ⟨U, V, f, g, _, hdeg, _, _, _, _, _, _, hf, hg, _, hamp⟩ := M.exists_ample_theta_quotient
  exact ⟨RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left, hamp,
    M.nativeThetaChernForm_integral U V f g hf hg hdeg, M.nativeThetaChernForm_trace U V f g hf hg hdeg⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
