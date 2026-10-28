import OAI.AlgebraicGeometry.Albanese.Construction.GeneratingForms
import OAI.AlgebraicGeometry.AbelianVariety.PureAverage
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectivePurePullback
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicPrimitive

/-! # Generated Antiholomorphic -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GeneratedAntiholomorphic.CM.Construction

noncomputable section

section

/-! A map generating an abelian variety detects the entire holomorphic
degree-one de Rham subspace, using genuine invariant representatives. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

theorem generated_holomorphic_deRham_kernel (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) (A : CMAbelianVariety.CM.AbelianVariety)
    (a : X.toOver ⟶ A.toOver) (hgen : Albanese.Construction.GeneratedClosed.Generates X.presentation A a)
    (c : A.variety.deRhamCohomology 1) (hc : c ∈ A.variety.pureDeRhamSubspace 1 0)
    (hzero : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback a 1 c = 0) : c = 0 := by
  let : ConnectedSpace A.variety.analyticSpace := AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPoint_connectedSpace A
  let : MeasurableSpace A.variety.analyticSpace := borel _
  let : BorelSpace A.variety.analyticSpace := ⟨rfl⟩
  let f : AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := A.variety.analyticModel)
      (G := A.variety.analyticSpace) 1 := (AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianInvariantDeRhamEquiv A 1).symm c
  have heq : AbelianVariety.InvariantCohomology.Constructions.Exterior.invariantDeRham 1 f = c :=
    (AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianInvariantDeRhamEquiv A 1).apply_symm_apply c
  have hmem : AbelianVariety.InvariantCohomology.Constructions.Exterior.invariantDeRham 1 f ∈
      AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.manifoldPureDeRhamImage A.variety.analyticModel A.variety.analyticSpace 1 0 :=
    heq.symm ▸ hc
  have hf : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree A.variety.analyticModel A.variety.analyticSpace 1 0 f.val.val :=
    (AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantDeRham_mem_pure_iff (E := A.variety.analyticModel)
      (G := A.variety.analyticSpace) (p := 1) (q := 0) f).mp hmem
  let u := Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a)
    (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map a ∞) 1 (AbelianVariety.InvariantCohomology.Constructions.Exterior.invariantClosedInclusion 1 f)
  have hu : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree X.analyticModel X.analyticSpace 1 0 u.val.val :=
    hf.pullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a) (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complex_contMDiff_map a ∞)
  have hclass : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass X.analyticModel X.analyticSpace 1 u = 0 := by
    have h := Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback_closedFormClass a 1
      (AbelianVariety.InvariantCohomology.Constructions.Exterior.invariantClosedInclusion 1 f)
    change Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback a 1 (AbelianVariety.InvariantCohomology.Constructions.Exterior.invariantDeRham 1 f) =
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass X.analyticModel X.analyticSpace 1 u at h
    rw [heq, hzero] at h
    exact h.symm
  have huz := HolomorphicPrimitive.CM.Construction.holomorphic_oneForm_eq_zero_of_class_eq_zero u hu hclass
  have hpull : Albanese.Construction.AnalyticPullback.nativePullback a 1 f.val = 0 := congrArg Subtype.val huz
  have hfzero := Albanese.Construction.GeneratingForms.generating_invariantOneForm_pullback_zero X.presentation A a f x₀ hgen hpull
  rw [← heq, hfzero, map_zero]

end

/-! A generating map also detects the entire antiholomorphic H¹ subspace. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

theorem generated_antiholomorphic_deRham_kernel (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) (A : CMAbelianVariety.CM.AbelianVariety)
    (a : X.toOver ⟶ A.toOver) (hgen : Albanese.Construction.GeneratedClosed.Generates X.presentation A a)
    (c : A.variety.deRhamCohomology 1) (hc : c ∈ A.variety.pureDeRhamSubspace 0 1)
    (hzero : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback a 1 c = 0) : c = 0 := by
  let : ConnectedSpace A.variety.analyticSpace := AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPoint_connectedSpace A
  let : MeasurableSpace A.variety.analyticSpace := borel _
  let : BorelSpace A.variety.analyticSpace := ⟨rfl⟩
  let f : AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := A.variety.analyticModel)
      (G := A.variety.analyticSpace) 1 := (AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianInvariantDeRhamEquiv A 1).symm c
  have heq : AbelianVariety.InvariantCohomology.Constructions.Exterior.invariantDeRham 1 f = c :=
    (AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianInvariantDeRhamEquiv A 1).apply_symm_apply c
  have hmem : AbelianVariety.InvariantCohomology.Constructions.Exterior.invariantDeRham 1 f ∈
      AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.manifoldPureDeRhamImage A.variety.analyticModel A.variety.analyticSpace 0 1 :=
    heq.symm ▸ hc
  have hf : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree A.variety.analyticModel A.variety.analyticSpace 0 1 f.val.val :=
    (AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantDeRham_mem_pure_iff (E := A.variety.analyticModel)
      (G := A.variety.analyticSpace) (p := 0) (q := 1) f).mp hmem
  let u := Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a)
    (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map a ∞) 1 (AbelianVariety.InvariantCohomology.Constructions.Exterior.invariantClosedInclusion 1 f)
  have hu : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree X.analyticModel X.analyticSpace 0 1 u.val.val :=
    hf.pullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a) (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complex_contMDiff_map a ∞)
  have hclass : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass X.analyticModel X.analyticSpace 1 u = 0 := by
    have h := Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback_closedFormClass a 1
      (AbelianVariety.InvariantCohomology.Constructions.Exterior.invariantClosedInclusion 1 f)
    change Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback a 1 (AbelianVariety.InvariantCohomology.Constructions.Exterior.invariantDeRham 1 f) =
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass X.analyticModel X.analyticSpace 1 u at h
    rw [heq, hzero] at h
    exact h.symm
  have huz := HolomorphicPrimitive.CM.Construction.antiholomorphic_oneForm_eq_zero_of_class_eq_zero u hu hclass
  have hpull : Albanese.Construction.AnalyticPullback.nativePullback a 1 f.val = 0 := congrArg Subtype.val huz
  have hfzero := Albanese.Construction.GeneratingForms.generating_invariantOneForm_pullback_zero X.presentation A a f x₀ hgen hpull
  rw [← heq, hfzero, map_zero]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GeneratedAntiholomorphic.CM.Construction
