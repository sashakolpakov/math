import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SurfacePairingIntegral
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RechartIntegrationClass
import OAI.AlgebraicTopology.Kunneth.ClosedManifoldWedge
import OAI.AlgebraicTopology.Kunneth.ProjectiveCupPurity

/-! # Surface Projective Pairing -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SurfaceProjectivePairing.CM

noncomputable section

section

/-! ThetaCycle: transfer the actual surface pairing to a singular class
represented by the native closed wedge in the original complex model. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open scoped _root_.Manifold ContDiff

variable {M : Type} [TopologicalSpace M] [ChartedSpace HeckeCycles.GeometricSource.CM.BallChart M]
  [IsManifold 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) ∞ M] [IsManifold 𝓘(ℂ, HeckeCycles.GeometricSource.CM.BallChart) 1 M]
  [T2Space M] [CompactSpace M]

theorem represented_surface_wedge_pairing
    (D : Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.FiniteChartPartition HeckeCycles.GeometricSource.CM.BallChart M) (α β : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms HeckeCycles.GeometricSource.CM.BallChart M 2)
    (hα : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart M 2 0 α.val.val)
    (hβ : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart M 2 0 β.val.val)
    (η : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of M) 4)
    (hη : HomologicalComplex.homologyMap
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction HeckeCycles.GeometricSource.CM.BallChart (ModuleCat.of ℂ ℂ) M) 4 η =
        AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap HeckeCycles.GeometricSource.CM.BallChart M 4
          (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass HeckeCycles.GeometricSource.CM.BallChart M 4
            (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge α (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm β)))) :
    ComplexRealFundamental.CM.realSimplexComplexMultiplicity 2 (Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv 2) •
      AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ) (TopCat.of M) 4 η
        (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℂ) (TopCat.of M) 4
          (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass 2 M)) =
      -Analysis.HodgeTheory.TopForms.Constructions.PolarizedPairing.topPairingWith D (Pi.basisFun ℂ (Fin 2)) α.val (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm β.val) := by
  let e := Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv 2
  let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
  let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
  let form := AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge α (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm β)
  have hrep := RechartIntegrationClass.CM.linear_rechart_preserves_betti_representation e 4 form η hη
  have hclass := AlgebraicTopology.FundamentalClass.TopEvaluation.IntegrationConstruction.topIntegrationClass_eq 4 M (RealModelForms.CM.linearRechartClosedForms e 4 form) η hrep
  rw [hclass]
  exact SurfacePairingIntegral.CM.canonical_surface_wedge_pairing D α.val β.val hα hβ

theorem represented_surface_wedge_evaluation_nonzero
    (α β : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms HeckeCycles.GeometricSource.CM.BallChart M 2)
    (hα : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart M 2 0 α.val.val)
    (hβ : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart M 2 0 β.val.val)
    (hp : SurfacePairing.CM.surfaceConjugatePairing α.val β.val ≠ 0)
    (η : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of M) 4)
    (hη : HomologicalComplex.homologyMap
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction HeckeCycles.GeometricSource.CM.BallChart (ModuleCat.of ℂ ℂ) M) 4 η =
        AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap HeckeCycles.GeometricSource.CM.BallChart M 4
          (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass HeckeCycles.GeometricSource.CM.BallChart M 4
            (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge α (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm β)))) :
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ) (TopCat.of M) 4 η
      (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℂ) (TopCat.of M) 4
        (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass 2 M)) ≠ 0 := by
  have h := represented_surface_wedge_pairing (Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.canonicalChartPartition HeckeCycles.GeometricSource.CM.BallChart M)
    α β hα hβ η hη
  intro hz
  rw [hz, smul_zero] at h
  exact hp (neg_eq_zero.mp h.symm)

end

section

/-! ThetaCycle: use a proved complex dimension equality to identify the native
analytic model with the two-dimensional surface model. All changes below
are transport along that equality on the same underlying manifold. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open scoped _root_.Manifold ContDiff

variable {d : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℂ) M]

@[instance_reducible]
def complexSurfaceChartedSpace (hd : d = 2) : ChartedSpace HeckeCycles.GeometricSource.CM.BallChart M := by
  subst d
  exact inferInstanceAs (ChartedSpace (Fin 2 → ℂ) M)

theorem complex_surface_real_manifold (hd : d = 2) (r : ℕ∞ω)
    [IsManifold 𝓘(ℝ, Fin d → ℂ) r M] :
    let _ := complexSurfaceChartedSpace (M := M) hd
    IsManifold 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) r M := by
  subst d
  exact inferInstanceAs (IsManifold 𝓘(ℝ, Fin 2 → ℂ) r M)

theorem complex_surface_complex_manifold (hd : d = 2) (r : ℕ∞ω)
    [IsManifold 𝓘(ℂ, Fin d → ℂ) r M] :
    let _ := complexSurfaceChartedSpace (M := M) hd
    IsManifold 𝓘(ℂ, HeckeCycles.GeometricSource.CM.BallChart) r M := by
  subst d
  exact inferInstanceAs (IsManifold 𝓘(ℂ, Fin 2 → ℂ) r M)

def complexSurfaceForms (hd : d = 2) (n : ℕ) :
    let _ := complexSurfaceChartedSpace (M := M) hd
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℂ) M n ≃ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart M n := by
  subst d
  exact LinearEquiv.refl ℂ _

theorem complex_surface_forms_pure (hd : d = 2) (p q : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℂ) M (p + q))
    (ht : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (Fin d → ℂ) M p q form.val) :
    let _ := complexSurfaceChartedSpace (M := M) hd
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart M p q (complexSurfaceForms hd (p + q) form).val := by
  subst d
  exact ht

variable [IsManifold 𝓘(ℝ, Fin d → ℂ) ∞ M]

def complexSurfaceClosedForms (hd : d = 2) (n : ℕ) :
    let _ := complexSurfaceChartedSpace (M := M) hd
    let _ : IsManifold 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) ∞ M := complex_surface_real_manifold (M := M) hd ∞
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (Fin d → ℂ) M n ≃ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms HeckeCycles.GeometricSource.CM.BallChart M n := by
  subst d
  exact LinearEquiv.refl ℂ _

theorem complex_surface_closed_forms_val (hd : d = 2) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (Fin d → ℂ) M n) :
    let _ := complexSurfaceChartedSpace (M := M) hd
    let _ : IsManifold 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) ∞ M := complex_surface_real_manifold (M := M) hd ∞
    (complexSurfaceClosedForms hd n form).val = complexSurfaceForms hd n form.val := by
  subst d
  rfl

theorem complex_surface_closed_wedge (hd : d = 2) (p q : ℕ)
    (α : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (Fin d → ℂ) M p) (β : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (Fin d → ℂ) M q) :
    let _ := complexSurfaceChartedSpace (M := M) hd
    let _ := complex_surface_real_manifold (M := M) hd ∞
    complexSurfaceClosedForms hd (p + q) (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge α β) =
      AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge (complexSurfaceClosedForms hd p α) (complexSurfaceClosedForms hd q β) := by
  subst d
  rfl

theorem complex_surface_closed_conjugate (hd : d = 2) (n : ℕ)
    (α : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (Fin d → ℂ) M n) :
    let _ := complexSurfaceChartedSpace (M := M) hd
    let _ := complex_surface_real_manifold (M := M) hd ∞
    complexSurfaceClosedForms hd n (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm α) =
      ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm (complexSurfaceClosedForms hd n α) := by
  subst d
  rfl

theorem complex_surface_betti_representation (hd : d = 2) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (Fin d → ℂ) M n)
    (η : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of M) n)
    (hη : HomologicalComplex.homologyMap
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction (Fin d → ℂ) (ModuleCat.of ℂ ℂ) M) n η =
        AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap (Fin d → ℂ) M n
          (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (Fin d → ℂ) M n form)) :
    let _ := complexSurfaceChartedSpace (M := M) hd
    let _ := complex_surface_real_manifold (M := M) hd ∞
    HomologicalComplex.homologyMap
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction HeckeCycles.GeometricSource.CM.BallChart (ModuleCat.of ℂ ℂ) M) n η =
        AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap HeckeCycles.GeometricSource.CM.BallChart M n
          (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass HeckeCycles.GeometricSource.CM.BallChart M n (complexSurfaceClosedForms hd n form)) := by
  subst d
  exact hη

variable [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

omit [IsManifold 𝓘(ℝ, Fin d → ℂ) ∞ M] in
theorem complex_surface_fundamental_class (hd : d = 2) :
    let _ := complexSurfaceChartedSpace (M := M) hd
    let _ : IsManifold 𝓘(ℂ, HeckeCycles.GeometricSource.CM.BallChart) 1 M := complex_surface_complex_manifold (M := M) hd 1
    (eqToHom (congrArg (fun n => (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of M)).homology n)
      (show 2 * d = 4 by rw [hd]))) (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass d M) =
      CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass 2 M := by
  subst d
  rfl

end

section

/-! ThetaCycle: the actual projective surface evaluation is detected by the
computed conjugate pairing of its native smooth forms. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open scoped _root_.Manifold ContDiff

def projectiveSurfaceConjugatePairing (S : Cm.ProjectiveSurface)
    (α β : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm S.variety.analyticModel S.variety.analyticSpace 2) : ℂ :=
  let _ := complexSurfaceChartedSpace (M := S.variety.analyticSpace) S.property
  let _ := complex_surface_real_manifold (M := S.variety.analyticSpace) S.property ∞
  SurfacePairing.CM.surfaceConjugatePairing (complexSurfaceForms S.property 2 α) (complexSurfaceForms S.property 2 β)

theorem projective_surface_self_pairing_nonzero (S : Cm.ProjectiveSurface)
    (α : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm S.variety.analyticModel S.variety.analyticSpace 2)
    (hα : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree S.variety.analyticModel S.variety.analyticSpace 2 0 α.val)
    (hne : α ≠ 0) : projectiveSurfaceConjugatePairing S α α ≠ 0 := by
  let _ := complexSurfaceChartedSpace (M := S.variety.analyticSpace) S.property
  let _ := complex_surface_real_manifold (M := S.variety.analyticSpace) S.property ∞
  have ht := complex_surface_forms_pure S.property 2 0 α hα
  have hn : complexSurfaceForms S.property 2 α ≠ 0 := by
    intro hz
    apply hne
    apply (complexSurfaceForms S.property 2).injective
    simpa only [map_zero] using hz
  exact (SurfacePairing.CM.surface_conjugate_pairing_positive (complexSurfaceForms S.property 2 α) ht hn).2.2

theorem projective_surface_represented_wedge_nonzero (S : Cm.ProjectiveSurface)
    (α β : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms S.variety.analyticModel S.variety.analyticSpace 2)
    (hα : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree S.variety.analyticModel S.variety.analyticSpace 2 0 α.val.val)
    (hβ : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree S.variety.analyticModel S.variety.analyticSpace 2 0 β.val.val)
    (hp : projectiveSurfaceConjugatePairing S α.val β.val ≠ 0)
    (η : S.variety.complexCohomology 4)
    (hη : HomologicalComplex.homologyMap
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction S.variety.analyticModel (ModuleCat.of ℂ ℂ)
        S.variety.analyticSpace) 4 η =
        AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap S.variety.analyticModel S.variety.analyticSpace 4
          (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass S.variety.analyticModel S.variety.analyticSpace 4
            (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge α (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm β)))) :
    S.evaluate η ≠ 0 := by
  let _ := complexSurfaceChartedSpace (M := S.variety.analyticSpace) S.property
  let _ := complex_surface_real_manifold (M := S.variety.analyticSpace) S.property ∞
  let _ := complex_surface_complex_manifold (M := S.variety.analyticSpace) S.property 1
  let α' := complexSurfaceClosedForms S.property 2 α
  let β' := complexSurfaceClosedForms S.property 2 β
  have ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart S.variety.analyticSpace 2 0 α'.val.val := by
    dsimp only [α']
    rw [complex_surface_closed_forms_val]
    exact complex_surface_forms_pure S.property 2 0 α.val hα
  have hb : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart S.variety.analyticSpace 2 0 β'.val.val := by
    dsimp only [β']
    rw [complex_surface_closed_forms_val]
    exact complex_surface_forms_pure S.property 2 0 β.val hβ
  have hrep := complex_surface_betti_representation S.property 4
    (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge α (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm β)) η hη
  dsimp only at hrep
  rw [complex_surface_closed_wedge S.property 2 2 α (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm β),
    complex_surface_closed_conjugate S.property 2 β] at hrep
  have hp' : SurfacePairing.CM.surfaceConjugatePairing α'.val β'.val ≠ 0 := by
    dsimp only [α', β']
    rw [complex_surface_closed_forms_val, complex_surface_closed_forms_val]
    exact hp
  have hn := represented_surface_wedge_evaluation_nonzero α' β' ha hb hp' η hrep
  have hc := complex_surface_fundamental_class (M := S.variety.analyticSpace) S.property
  rw [Cm.ProjectiveSurface.evaluate_eq]
  change AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ) (TopCat.of S.variety.analyticSpace) 4 η
    (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℂ) (TopCat.of S.variety.analyticSpace) 4
      S.integralClass) ≠ 0
  have he : S.integralClass = CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass 2 S.variety.analyticSpace := hc
  rw [he]
  exact hn

theorem projective_surface_cup_evaluation_nonzero (S : Cm.ProjectiveSurface)
    (α β : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms S.variety.analyticModel S.variety.analyticSpace 2)
    (hα : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree S.variety.analyticModel S.variety.analyticSpace 2 0 α.val.val)
    (hβ : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree S.variety.analyticModel S.variety.analyticSpace 2 0 β.val.val)
    (hp : projectiveSurfaceConjugatePairing S α.val β.val ≠ 0) :
    S.evaluate (Cm.cup S.variety 2 2 (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass S.variety 2 α)
      (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass S.variety 2 (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm β))) ≠ 0 := by
  apply projective_surface_represented_wedge_nonzero S α β hα hβ hp
  rw [← AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass_wedge]
  rw [AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCohomologyMap_formClass]
  simpa only [AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass] using!
    S.variety.deRhamBettiIso_formClass 4 (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge α (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm β))

theorem projective_surface_self_cup_evaluation_nonzero (S : Cm.ProjectiveSurface)
    (α : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms S.variety.analyticModel S.variety.analyticSpace 2)
    (hα : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree S.variety.analyticModel S.variety.analyticSpace 2 0 α.val.val)
    (hne : α.val ≠ 0) :
    S.evaluate (Cm.cup S.variety 2 2 (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass S.variety 2 α)
      (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass S.variety 2 (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm α))) ≠ 0 :=
  projective_surface_cup_evaluation_nonzero S α α hα hα
    (projective_surface_self_pairing_nonzero S α.val hα hne)

end

/-! ThetaCycle: an exact pure holomorphic top form on the actual projective
surface vanishes, by native Betti comparison and the proved self-pairing. -/

open scoped _root_.Manifold ContDiff

theorem projective_surface_pure_exact_top_zero (S : Cm.ProjectiveSurface)
    (α : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms S.variety.analyticModel S.variety.analyticSpace 2)
    (ht : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree S.variety.analyticModel S.variety.analyticSpace 2 0 α.val.val)
    (primitive : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm S.variety.analyticModel S.variety.analyticSpace 1)
    (hprimitive : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d primitive = α.val) : α.val = 0 := by
  by_contra hn
  have he := projective_surface_self_cup_evaluation_nonzero S α ht hn
  have hz : S.variety.deRhamClass 2 α = 0 :=
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass_eq_zero_iff S.variety.analyticModel S.variety.analyticSpace 2 α).mpr
      ⟨primitive, hprimitive⟩
  have hb : AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass S.variety 2 α = 0 := by
    rw [AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass, hz]
    exact map_zero _
  rw [hb] at he
  exact he (by simp only [map_zero, LinearMap.zero_apply])

theorem projective_surface_one_form_closed_of_derivative_pure (S : Cm.ProjectiveSurface)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm S.variety.analyticModel S.variety.analyticSpace 1)
    (ht : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree S.variety.analyticModel S.variety.analyticSpace 2 0
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0 :=
  projective_surface_pure_exact_top_zero S ⟨Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_squared a⟩
    ht a rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SurfaceProjectivePairing.CM
