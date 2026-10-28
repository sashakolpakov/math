import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientConstantForms
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothPeriodMap
import OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback
import OAI.Analysis.DifferentialForms.Manifold.ClosedPullback

/-! # Period Map -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodMap.CM.Construction

noncomputable section

section

/-! Coordinate formulas for the actual pullback of constant quotient
forms and for differentials of the primitive vectors. -/

open Filter
open scoped _root_.Manifold ContDiff _root_.Topology

open scoped OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientManifold.CM.Construction.ComplexLatticeQuotient OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientTangentCoordinates.CM.Construction.ComplexLatticeQuotient

theorem constantQuotientForm_lift_pullback_inChart
    {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (Λ : AddSubgroup F) [DiscreteTopology Λ] {n : ℕ} (a : Analysis.DifferentialForms.Manifold.Basic.FormValue F n)
    (g : M → F) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (z : E) (hz : z ∈ e.target) :
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback
      ((QuotientAddGroup.mk : F → QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ) ∘ g)
      ((QuotientTangentCoordinates.CM.Construction.ComplexLatticeQuotient.projection_realContMDiff Λ).comp hg)
      (QuotientConstantForms.CM.Construction.ComplexLatticeQuotient.constantQuotientForm Λ a)).val.inChart e z =
      a.compContinuousLinearMap (fderiv ℝ (g ∘ e.symm) z) := by
  let q : QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ := QuotientAddGroup.mk (g (e.symm z))
  let c := QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ q
  have hc : c ∈ atlas F (QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ) :=
    QuotientTangentCoordinates.CM.Construction.ComplexLatticeQuotient.quotientChart_mem_atlas Λ q
  have hq : q ∈ c.source := QuotientManifold.CM.Construction.ComplexLatticeQuotient.mem_quotientChart_source Λ q
  have hmap := ((QuotientTangentCoordinates.CM.Construction.ComplexLatticeQuotient.projection_realContMDiff Λ).comp hg).mdifferentiableAt
    (x := e.symm z) (by simp)
  change ((QuotientConstantForms.CM.Construction.ComplexLatticeQuotient.constantQuotientRaw Λ a).pullback
    ((QuotientAddGroup.mk : F → QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ) ∘ g)).inChart e z = _
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.pullback_inChart _ _ e c he hc hz hq hmap]
  have hconst : (QuotientConstantForms.CM.Construction.ComplexLatticeQuotient.constantQuotientRaw Λ a).inChart c
      (c ((QuotientAddGroup.mk ∘ g) (e.symm z))) = a :=
    QuotientConstantForms.CM.Construction.ComplexLatticeQuotient.constantQuotientRaw_inChart Λ a q _ (c.map_source hq)
  rw [hconst]
  have hd : DifferentiableAt ℝ (g ∘ e.symm) z := by
    have h := Analysis.DifferentialForms.Manifold.ManifoldPullback.contDiffAt_manifoldMap_inChart g e (OpenPartialHomeomorph.refl F)
      he (by simp) hz (by trivial) hg.contMDiffAt
    exact h.differentiableAt (by simp)
  have hsection := QuotientTangentCoordinates.CM.Construction.ComplexLatticeQuotient.quotientSection_hasFDerivAt Λ c
    (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart_symm Λ q) (g (e.symm z)) hq
  have hder := (hsection.comp z hd.hasFDerivAt).fderiv
  simpa only [ContinuousLinearMap.id_comp, Function.comp_def] using congrArg
    (fun L : E →L[ℝ] F => a.compContinuousLinearMap L) hder

theorem primitive_scalar_fderiv
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (z : E) (hz : z ∈ e.target) (u : E) :
    fderiv ℝ (HolomorphicPrimitive.CM.Construction.zeroFormScalar f ∘ e.symm) z u =
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f).val.inChart e z (fun _ => u) := by
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart f e he hz, HolomorphicPrimitive.CM.Construction.zeroFormScalar_reconstruct,
    extDeriv_constOfIsEmpty]
  rfl

theorem primitive_vector_fderiv
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {ι : Type} [Fintype ι] (f : ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (z : E) (hz : z ∈ e.target) (u : E) :
    fderiv ℝ (fun w => fun i => HolomorphicPrimitive.CM.Construction.zeroFormScalar (f i) (e.symm w)) z u =
      fun i => (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (f i)).val.inChart e z (fun _ => u) := by
  have hd (i : ι) := (HolomorphicPrimitive.CM.Construction.zeroFormScalar_contDiffAt_inChart (f i) e he hz).differentiableAt (by simp)
  calc
    _ = fun i => fderiv ℝ (HolomorphicPrimitive.CM.Construction.zeroFormScalar (f i) ∘ e.symm) z u :=
      congrArg (fun L : E →L[ℝ] (ι → ℂ) => L u) (fderiv_pi hd)
    _ = _ := funext (fun i => primitive_scalar_fderiv (f i) e he z hz u)

end

section

/-! Real coordinate covectors on the period space recover the
canonical real differentials from every local lift of the period map. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open scoped OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientManifold.CM.Construction.ComplexLatticeQuotient OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientTangentCoordinates.CM.Construction.ComplexLatticeQuotient

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {ι : Type} [Fintype ι]
  (b : Module.Basis ι ℚ (V.rationalCohomology 1))

def rationalPeriodCoordinateCovector (i : ι) : PeriodLattice.CM.Construction.RationalH1PeriodSpace V b →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp ((ContinuousLinearMap.proj i).comp
    ⟨(PeriodLattice.CM.Construction.rationalPeriodRealEquiv V b).symm.toLinearMap,
      LinearMap.continuous_of_finiteDimensional _⟩)

theorem rationalPeriodCoordinateCovector_real (i : ι) (r : ι → ℝ) :
    rationalPeriodCoordinateCovector V b i (PeriodLattice.CM.Construction.rationalPeriodProjection V b (fun j => (r j : ℂ))) =
      (r i : ℂ) := by
  rw [PeriodLattice.CM.Construction.rationalPeriodProjection_real]
  change (((PeriodLattice.CM.Construction.rationalPeriodRealEquiv V b).symm (PeriodLattice.CM.Construction.rationalPeriodRealEquiv V b r)) i : ℂ) = _
  rw [LinearEquiv.symm_apply_apply]

theorem rationalPeriodCoordinateCovector_of_real (i : ι) (r : ι → ℂ)
    (hr : ∀ j, (r j).im = 0) :
    rationalPeriodCoordinateCovector V b i (PeriodLattice.CM.Construction.rationalPeriodProjection V b r) = r i := by
  have heq : (fun j => ((r j).re : ℂ)) = r := by
    funext j
    apply Complex.ext
    · rfl
    · exact (hr j).symm
  have h := rationalPeriodCoordinateCovector_real V b i (fun j => (r j).re)
  rw [heq] at h
  exact h.trans (congrFun heq i)

theorem period_coordinate_primitive_pullback
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (f : ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0)
    (hreal : ∀ i x (v : Fin 1 → TangentSpace 𝓘(ℝ, E) x),
      ((Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (f i)) x v).im = 0) (i : ι) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback
      (fun x : M => (QuotientAddGroup.mk
        (PeriodLattice.CM.Construction.rationalPeriodProjection V b (fun j => HolomorphicPrimitive.CM.Construction.zeroFormScalar (f j) x)) : PeriodLattice.CM.Construction.RationalH1PeriodTorus V b))
      ((QuotientTangentCoordinates.CM.Construction.ComplexLatticeQuotient.projection_realContMDiff (PeriodLattice.CM.Construction.rationalPeriodLattice V b).toAddSubgroup).comp
        ((PeriodLattice.CM.Construction.rationalPeriodProjection V b).restrictScalars ℝ |>.contDiff.comp_contMDiff
          (SmoothPeriodMap.CM.Construction.contMDiff_finite_coordinates _ (fun j => SmoothPeriodMap.CM.Construction.zeroFormScalar_contMDiff (f j)))))
      (QuotientConstantForms.CM.Construction.ComplexLatticeQuotient.constantQuotientClosedOneForm (PeriodLattice.CM.Construction.rationalPeriodLattice V b).toAddSubgroup
        (rationalPeriodCoordinateCovector V b i)).val = Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (f i) := by
  let L := (PeriodLattice.CM.Construction.rationalPeriodProjection V b).restrictScalars ℝ
  let g : M → PeriodLattice.CM.Construction.RationalH1PeriodSpace V b :=
    fun x => PeriodLattice.CM.Construction.rationalPeriodProjection V b (fun j => HolomorphicPrimitive.CM.Construction.zeroFormScalar (f j) x)
  have hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, PeriodLattice.CM.Construction.RationalH1PeriodSpace V b) ∞ g :=
    L.contDiff.comp_contMDiff (SmoothPeriodMap.CM.Construction.contMDiff_finite_coordinates _ (fun j => SmoothPeriodMap.CM.Construction.zeroFormScalar_contMDiff (f j)))
  let a := ContinuousAlternatingMap.ofSubsingleton ℝ (PeriodLattice.CM.Construction.RationalH1PeriodSpace V b) ℂ
    (0 : Fin 1) (rationalPeriodCoordinateCovector V b i)
  let π := (QuotientAddGroup.mk : PeriodLattice.CM.Construction.RationalH1PeriodSpace V b → PeriodLattice.CM.Construction.RationalH1PeriodTorus V b)
  let hp := (QuotientTangentCoordinates.CM.Construction.ComplexLatticeQuotient.projection_realContMDiff
    (PeriodLattice.CM.Construction.rationalPeriodLattice V b).toAddSubgroup).comp hg
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (π ∘ g) hp
    (QuotientConstantForms.CM.Construction.ComplexLatticeQuotient.constantQuotientForm (PeriodLattice.CM.Construction.rationalPeriodLattice V b).toAddSubgroup a) = _
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  let e := chartAt E x
  have he : e ∈ atlas E M := chart_mem_atlas E x
  have hx : x ∈ e.source := mem_chart_source E x
  have hz : e x ∈ e.target := e.map_source hx
  have hchart : (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (π ∘ g) hp
      (QuotientConstantForms.CM.Construction.ComplexLatticeQuotient.constantQuotientForm
        (PeriodLattice.CM.Construction.rationalPeriodLattice V b).toAddSubgroup a)).val.inChart e (e x) =
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (f i)).val.inChart e (e x) := by
    rw [constantQuotientForm_lift_pullback_inChart _ a g hg e he (e x) hz]
    ext v
    change rationalPeriodCoordinateCovector V b i
      (fderiv ℝ (g ∘ e.symm) (e x) (v 0)) = _
    have hvec (j : ι) :=
      (HolomorphicPrimitive.CM.Construction.zeroFormScalar_contDiffAt_inChart (f j) e he hz).differentiableAt (by simp)
    have hd := (L.hasFDerivAt.comp (e x) (differentiableAt_pi.mpr hvec).hasFDerivAt).fderiv
    have hd' : fderiv ℝ (g ∘ e.symm) (e x) =
        L.comp (fderiv ℝ (fun w => fun j => HolomorphicPrimitive.CM.Construction.zeroFormScalar (f j) (e.symm w)) (e x)) := hd
    rw [hd']
    change rationalPeriodCoordinateCovector V b i (PeriodLattice.CM.Construction.rationalPeriodProjection V b
      (fderiv ℝ (fun w => fun j => HolomorphicPrimitive.CM.Construction.zeroFormScalar (f j) (e.symm w)) (e x) (v 0))) = _
    rw [primitive_vector_fderiv f e he (e x) hz (v 0)]
    have hr : ∀ j, ((Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (f j)).val.inChart e (e x) (fun _ => v 0)).im = 0 :=
      fun j => hreal j _ _
    rw [rationalPeriodCoordinateCovector_of_real V b i
      (fun j => (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (f j)).val.inChart e (e x) (fun _ => v 0)) hr]
    apply congrArg ((Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (f i)).val.inChart e (e x))
    funext j
    exact congrArg v (Fin.ext (by omega))
  have h := congrArg (fun a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 => a.compContinuousLinearMap (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x)) hchart
  simpa only [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_comp_chartTangentMap _ e he hx] using h

end

section

/-! The global period map pulls the constant coordinate forms back
to the integer multiples of the canonical rational representatives. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open scoped OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientManifold.CM.Construction.ComplexLatticeQuotient OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientTangentCoordinates.CM.Construction.ComplexLatticeQuotient

theorem smoothManifoldForm_eq_of_local_restrictions
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {n : ℕ} (a c : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (h : ∀ x : M, ∃ U : Opens M, x ∈ U ∧ Intersection.CM.Construction.restrictSmoothForm U n a = Intersection.CM.Construction.restrictSmoothForm U n c) :
    a = c := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  have heq : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U a = Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U c := by
    apply (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n).injective
    rw [Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_onOpen, Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_onOpen]
    exact hU
  exact congrArg (fun f : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n => f ⟨x, hx⟩) heq

theorem canonical_primitive_real (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (U : Opens V.analyticSpace) (d : ℤ) (q : V.rationalCohomology 1)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel U 0)
    (hf : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f = d • Intersection.CM.Construction.restrictSmoothForm U 1 (CanonicalRealOneForms.CM.Construction.canonicalRationalOneRepresentative V q).val)
    (x : U) (v : Fin 1 → TangentSpace 𝓘(ℝ, V.analyticModel) x) :
    ((Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f) x v).im = 0 := by
  rw [hf]
  change Complex.imAddGroupHom (d • ((CanonicalRealOneForms.CM.Construction.canonicalRationalOneRepresentative V q).val (x : V.analyticSpace)
    (fun i => mfderiv 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, V.analyticModel)
      (Subtype.val : U → V.analyticSpace) x (v i)))) = 0
  rw [map_zsmul]
  have h := CanonicalRealOneForms.CM.Construction.canonicalRationalOneRepresentative_im_zero V q (x : V.analyticSpace)
    (fun i => mfderiv 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, V.analyticModel)
      (Subtype.val : U → V.analyticSpace) x (v i))
  change d • ((CanonicalRealOneForms.CM.Construction.canonicalRationalOneRepresentative V q).val (x : V.analyticSpace)
    (fun i => mfderiv 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, V.analyticModel)
      (Subtype.val : U → V.analyticSpace) x (v i))).im = 0
  rw [h, smul_zero]

theorem period_map_pullback_coordinate (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ (V.rationalCohomology 1))
    (d : ℤ) (p : V.analyticSpace → PeriodLattice.CM.Construction.RationalH1PeriodTorus V b)
    (hp : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, PeriodLattice.CM.Construction.RationalH1PeriodSpace V b) ∞ p)
    (hlocal : ∀ x : V.analyticSpace, ∃ U : Opens V.analyticSpace, x ∈ U ∧
      ∃ f : ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel U 0,
        (∀ i, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (f i) =
          d • Intersection.CM.Construction.restrictSmoothForm U 1 (CanonicalRealOneForms.CM.Construction.canonicalRationalOneRepresentative V (b i)).val) ∧
        ∀ y : U, p y.val = QuotientAddGroup.mk
          (PeriodLattice.CM.Construction.rationalPeriodProjection V b (fun i => HolomorphicPrimitive.CM.Construction.zeroFormScalar (f i) y))) (i : ι) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback p hp
      (QuotientConstantForms.CM.Construction.ComplexLatticeQuotient.constantQuotientClosedOneForm (PeriodLattice.CM.Construction.rationalPeriodLattice V b).toAddSubgroup
        (rationalPeriodCoordinateCovector V b i)).val =
      d • (CanonicalRealOneForms.CM.Construction.canonicalRationalOneRepresentative V (b i)).val := by
  apply smoothManifoldForm_eq_of_local_restrictions
  intro x
  obtain ⟨U, hx, f, hf, hU⟩ := hlocal x
  refine ⟨U, hx, ?_⟩
  let c := (QuotientConstantForms.CM.Construction.ComplexLatticeQuotient.constantQuotientClosedOneForm
    (PeriodLattice.CM.Construction.rationalPeriodLattice V b).toAddSubgroup (rationalPeriodCoordinateCovector V b i)).val
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (Subtype.val : U → V.analyticSpace)
    (contMDiff_subtype_val (I := 𝓘(ℝ, V.analyticModel)) (n := ∞))
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback p hp c) = _
  rw [← Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp]
  have hmap : p ∘ (Subtype.val : U → V.analyticSpace) =
      fun y : U => (QuotientAddGroup.mk
        (PeriodLattice.CM.Construction.rationalPeriodProjection V b (fun j => HolomorphicPrimitive.CM.Construction.zeroFormScalar (f j) y)) : PeriodLattice.CM.Construction.RationalH1PeriodTorus V b) :=
    funext hU
  have hl := period_coordinate_primitive_pullback V b f
    (fun j y v => canonical_primitive_real V U d (b j) (f j) (hf j) y v) i
  refine Eq.trans ?_ (hl.trans ?_)
  · apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    intro y
    exact congrFun (congrArg (fun g : U → PeriodLattice.CM.Construction.RationalH1PeriodTorus V b =>
      c.val.pullback (E := V.analyticModel) g) hmap) y
  · exact (hf i).trans (map_zsmul (Intersection.CM.Construction.restrictSmoothForm U 1) d
      (CanonicalRealOneForms.CM.Construction.canonicalRationalOneRepresentative V (b i)).val).symm

theorem exists_period_map_with_coordinate_pullback (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ (V.rationalCohomology 1)) :
    ∃ d : ℤ, 0 < d ∧ ∃ p : C(V.analyticSpace, PeriodLattice.CM.Construction.RationalH1PeriodTorus V b),
      MDifferentiable 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, PeriodLattice.CM.Construction.RationalH1PeriodSpace V b) p ∧
      ∃ hp : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, PeriodLattice.CM.Construction.RationalH1PeriodSpace V b) ∞ p,
        ∀ i, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback p hp
          (QuotientConstantForms.CM.Construction.ComplexLatticeQuotient.constantQuotientClosedOneForm (PeriodLattice.CM.Construction.rationalPeriodLattice V b).toAddSubgroup
            (rationalPeriodCoordinateCovector V b i)).val =
            d • (CanonicalRealOneForms.CM.Construction.canonicalRationalOneRepresentative V (b i)).val := by
  obtain ⟨d, hd, p, hhol, hp, hlocal⟩ := SmoothPeriodMap.CM.Construction.exists_smooth_holomorphic_rationalH1_period_map V b
  exact ⟨d, hd, p, hhol, hp, period_map_pullback_coordinate V b d p hp hlocal⟩

end

/-! The constructed compact complex period quotient receives a
holomorphic map whose actual degree-one cohomology pullback is surjective. -/

open scoped _root_.Manifold ContDiff

open scoped OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientManifold.CM.Construction.ComplexLatticeQuotient OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientTangentCoordinates.CM.Construction.ComplexLatticeQuotient

theorem period_map_coordinate_class (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ (V.rationalCohomology 1))
    (d : ℤ) (p : V.analyticSpace → PeriodLattice.CM.Construction.RationalH1PeriodTorus V b)
    (hp : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, PeriodLattice.CM.Construction.RationalH1PeriodSpace V b) ∞ p)
    (i : ι)
    (hi : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback p hp
      (QuotientConstantForms.CM.Construction.ComplexLatticeQuotient.constantQuotientClosedOneForm (PeriodLattice.CM.Construction.rationalPeriodLattice V b).toAddSubgroup
        (rationalPeriodCoordinateCovector V b i)).val =
      d • (CanonicalRealOneForms.CM.Construction.canonicalRationalOneRepresentative V (b i)).val) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback p hp 1
      (QuotientConstantForms.CM.Construction.ComplexLatticeQuotient.constantQuotientH1 (PeriodLattice.CM.Construction.rationalPeriodLattice V b).toAddSubgroup
        (rationalPeriodCoordinateCovector V b i)) =
      d • V.deRhamClass 1 (CanonicalRealOneForms.CM.Construction.canonicalRationalOneRepresentative V (b i)) := by
  let c := QuotientConstantForms.CM.Construction.ComplexLatticeQuotient.constantQuotientClosedOneForm
    (PeriodLattice.CM.Construction.rationalPeriodLattice V b).toAddSubgroup (rationalPeriodCoordinateCovector V b i)
  let a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1 :=
    CanonicalRealOneForms.CM.Construction.canonicalRationalOneRepresentative V (b i)
  have hforms : Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback p hp 1 c = d • a := Subtype.ext hi
  change Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback p hp 1
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (PeriodLattice.CM.Construction.RationalH1PeriodSpace V b) (PeriodLattice.CM.Construction.RationalH1PeriodTorus V b) 1 c) =
      d • Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass V.analyticModel V.analyticSpace 1 a
  rw [Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldDeRhamFormClass_pullback_apply, hforms, map_zsmul]

theorem period_map_h1_surjective_of_coordinate_pullback (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ (V.rationalCohomology 1))
    (d : ℤ) (hd : 0 < d) (p : V.analyticSpace → PeriodLattice.CM.Construction.RationalH1PeriodTorus V b)
    (hp : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, PeriodLattice.CM.Construction.RationalH1PeriodSpace V b) ∞ p)
    (hforms : ∀ i, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback p hp
      (QuotientConstantForms.CM.Construction.ComplexLatticeQuotient.constantQuotientClosedOneForm (PeriodLattice.CM.Construction.rationalPeriodLattice V b).toAddSubgroup
        (rationalPeriodCoordinateCovector V b i)).val =
      d • (CanonicalRealOneForms.CM.Construction.canonicalRationalOneRepresentative V (b i)).val) :
    Function.Surjective (Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback p hp 1) := by
  let T := (V.deRhamBettiIso 1).hom.hom.comp (Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback p hp 1).hom
  let B := RationalCoordinates.CM.Construction.rationalH1ComplexBasis V b
  let c : ι → Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology (PeriodLattice.CM.Construction.RationalH1PeriodSpace V b) (PeriodLattice.CM.Construction.RationalH1PeriodTorus V b) 1 :=
    fun i => QuotientConstantForms.CM.Construction.ComplexLatticeQuotient.constantQuotientH1 (PeriodLattice.CM.Construction.rationalPeriodLattice V b).toAddSubgroup
      (rationalPeriodCoordinateCovector V b i)
  have hTc (i : ι) : T (c i) = d • B i := by
    let a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1 :=
      CanonicalRealOneForms.CM.Construction.canonicalRationalOneRepresentative V (b i)
    have hclass : Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback p hp 1 (c i) = d • V.deRhamClass 1 a :=
      period_map_coordinate_class V b d p hp i (hforms i)
    change (V.deRhamBettiIso 1).hom (Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback p hp 1 (c i)) = _
    rw [hclass, map_zsmul]
    exact congrArg (fun z : V.complexCohomology 1 => d • z)
      ((CanonicalRealOneForms.CM.Construction.canonicalRationalOneRepresentative_class V (b i)).trans
        (RationalCoordinates.CM.Construction.rationalH1ComplexBasis_apply V b i).symm)
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  have hB (i : ι) : B i ∈ LinearMap.range T := by
    refine ⟨(d : ℂ)⁻¹ • c i, ?_⟩
    rw [map_smul, hTc, ← Int.cast_smul_eq_zsmul ℂ, inv_smul_smul₀ hdC]
  have hsurj : Function.Surjective T := by
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← B.span_eq]
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hB i)
  intro a
  obtain ⟨t, ht⟩ := hsurj ((V.deRhamBettiIso 1).hom a)
  refine ⟨t, (V.deRhamBettiIso 1).toLinearEquiv.injective ht⟩

theorem exists_holomorphic_period_map_h1_surjective (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ (V.rationalCohomology 1)) :
    ∃ p : C(V.analyticSpace, PeriodLattice.CM.Construction.RationalH1PeriodTorus V b),
      MDifferentiable 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, PeriodLattice.CM.Construction.RationalH1PeriodSpace V b) p ∧
      ∃ hp : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, PeriodLattice.CM.Construction.RationalH1PeriodSpace V b) ∞ p,
        Function.Surjective (Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback p hp 1) := by
  obtain ⟨d, hd, p, hhol, hp, hforms⟩ := exists_period_map_with_coordinate_pullback V b
  exact ⟨p, hhol, hp, period_map_h1_surjective_of_coordinate_pullback V b d hd p hp hforms⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodMap.CM.Construction
