import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverPullback
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverDerivative
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import OAI.Analysis.DifferentialForms.Manifold.LocalPullback

/-! # Cover Local M -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverLocalM.CM

noncomputable section

section

/-! ThetaCycle: actual smooth local inverses of the constructed principal ball covers. -/

open scoped Classical _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

theorem complex_contMDiffOn_of_mdifferentiableOn
    {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ∞ N]
    (f : M → N) (U : TopologicalSpace.Opens M)
    (hf : MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, F) f U) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f U := by
  have hr : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) (fun x : U => f x) := by
    intro x
    exact ((hf x x.property).mdifferentiableAt (U.isOpen.mem_nhds x.property)).comp x
      ((contMDiff_subtype_val (I := 𝓘(ℂ, E)) (n := (1 : ℕ∞ω)) (U := U)).mdifferentiableAt one_ne_zero)
  have hs := OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hr
  intro x hx
  exact (contMDiffAt_subtype_iff.mp (hs (⟨x, hx⟩ : U))).contMDiffWithinAt

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [NumberField.IsCMField K]
  (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N : ℕ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (π : B.Domain → X.analyticSpace) (hπ : B.IsBallCover N X π)

include hπ

theorem ball_cover_local_diffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ, HeckeCycles.GeometricSource.CM.BallChart) 𝓘(ℂ, X.analyticModel) ∞ π := by
  intro x
  obtain ⟨e, hx, he⟩ := hπ.2.2.1.isLocalHomeomorph x
  have hi : MDifferentiableOn 𝓘(ℂ, X.analyticModel) 𝓘(ℂ, HeckeCycles.GeometricSource.CM.BallChart) e.symm e.target := by
    intro y hy
    have h := HeckeCycles.CoverDerivative.CM.mdifferentiableAt_local_inverse e (e.map_target hy)
      (he ▸ hπ.2.2.2.1 (e.symm y)) (he ▸ hπ.2.2.2.2.1 (e.symm y))
    rw [e.right_inv hy] at h
    exact h.mdifferentiableWithinAt
  let φ : PartialDiffeomorph 𝓘(ℂ, HeckeCycles.GeometricSource.CM.BallChart) 𝓘(ℂ, X.analyticModel) B.Domain X.analyticSpace ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := by
        change ContMDiffOn 𝓘(ℂ, HeckeCycles.GeometricSource.CM.BallChart) 𝓘(ℂ, X.analyticModel) ∞ e e.source
        rw [← he]
        exact (CoverPullback.CM.ball_cover_complex_smooth K B N X π hπ).contMDiffOn
      contMDiffOn_invFun := complex_contMDiffOn_of_mdifferentiableOn e.symm ⟨e.target, e.open_target⟩ hi }
  refine ⟨φ, hx, ?_⟩
  intro y _
  exact congrFun he y

theorem ball_cover_real_local_diffeomorph :
    IsLocalDiffeomorph 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) 𝓘(ℝ, X.analyticModel) ∞ π := by
  intro x
  obtain ⟨φ, hx, he⟩ := ball_cover_local_diffeomorph K B N X π hπ x
  let ψ : PartialDiffeomorph 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) 𝓘(ℝ, X.analyticModel) B.Domain X.analyticSpace ∞ :=
    { toPartialEquiv := φ.toPartialEquiv
      open_source := φ.open_source
      open_target := φ.open_target
      contMDiffOn_toFun := fun z hz =>
        (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiffAt_real_of_complex ((φ.contMDiffOn_toFun z hz).contMDiffAt
          (φ.open_source.mem_nhds hz))).contMDiffWithinAt
      contMDiffOn_invFun := fun z hz =>
        (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiffAt_real_of_complex ((φ.contMDiffOn_invFun z hz).contMDiffAt
          (φ.open_target.mem_nhds hz))).contMDiffWithinAt }
  exact ⟨ψ, hx, he⟩

end

section

/-! ThetaCycle: actual descent of covector fields along a surjective local
diffeomorphism. Fiber compatibility concerns transported tangent covectors;
the descended form and its smoothness are constructed. -/

open scoped Classical _root_.Manifold ContDiff _root_.Topology
open Set Filter

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
theorem raw_pullback_local_section (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (s : N → M)
    (U : Set N) (hU : IsOpen U) (hs : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ s U)
    (hfs : ∀ y ∈ U, f (s y) = y) (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm F N n)
    (y : N) (hy : y ∈ U) :
    (a.pullback (E := E) f).pullback s y = a y := by
  have hsAt := ((hs y hy).contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have he : (f ∘ s) =ᶠ[𝓝 y] id := eventuallyEq_of_mem (hU.mem_nhds hy) hfs
  have hd : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (s y)).comp
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) s y) = ContinuousLinearMap.id ℝ F := by
    rw [← mfderiv_comp y (hf.mdifferentiableAt (by simp)) hsAt, he.mfderiv_eq, mfderiv_id]
    rfl
  ext v
  change a (f (s y)) (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (s y)
    (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) s y (v i))) = a y v
  have hv : (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (s y)
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) s y (v i))) = v := by
    funext i
    exact congrArg (fun L : F →L[ℝ] F => L (v i)) hd
  rw [hv, hfs y hy]

theorem raw_form_smooth_of_cover_pullback (f : M → N)
    (hs : Function.Surjective f) (hf : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm F N n)
    (ha : Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (a.pullback (E := E) f) univ) :
    Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn a univ := by
  have hlocal : ∀ y : N, ∃ U : Set N, y ∈ U ∧ IsOpen U ∧ Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn a U := by
    intro y
    obtain ⟨x, rfl⟩ := hs y
    obtain ⟨φ, hx, he⟩ := hf x
    have htarget : f x ∈ φ.target := by rw [he hx]; exact φ.map_source hx
    have hsection : ∀ y ∈ φ.target, f (φ.symm y) = y := by
      intro y hy
      exact (he (φ.map_target hy)).trans (φ.right_inv hy)
    refine ⟨φ.target, htarget, φ.open_target, ?_⟩
    have hp := (a.pullback (E := E) f).pullback_smooth_on φ.open_target isOpen_univ ha
      φ.symm φ.contMDiffOn_invFun (fun _ _ => mem_univ _)
    exact hp.congr (fun y hy => raw_pullback_local_section f hf.contMDiff φ.symm φ.target
      φ.open_target φ.contMDiffOn_invFun hsection n a y hy)
  choose U hmem hopen hsmooth using hlocal
  exact Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn.of_openCover hsmooth hopen (fun y => ⟨y, hmem y⟩)

def coverFiberCovector (f : M → N)
    (hf : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n) (x : M) : Analysis.DifferentialForms.Manifold.Basic.FormValue F n :=
  (a x).compContinuousLinearMap
    (hf.mfderivToContinuousLinearEquiv (by simp) x).symm.toContinuousLinearMap

def coverRawDescent (f : M → N) (hs : Function.Surjective f)
    (hf : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n) : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm F N n :=
  fun y => coverFiberCovector f hf n a (hs y).choose

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
theorem cover_raw_descent_pullback (f : M → N) (hs : Function.Surjective f)
    (hf : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n)
    (hcompat : ∀ x y, f x = f y → coverFiberCovector f hf n a x = coverFiberCovector f hf n a y) :
    (coverRawDescent f hs hf n a).pullback f = a := by
  funext x
  have he : coverRawDescent f hs hf n a (f x) = coverFiberCovector f hf n a x :=
    hcompat _ x (hs (f x)).choose_spec
  ext v
  change coverRawDescent f hs hf n a (f x) (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x (v i)) = a x v
  rw [he]
  change a x (fun i => (hf.mfderivToContinuousLinearEquiv (by simp) x).symm
    ((hf.mfderivToContinuousLinearEquiv (by simp) x) (v i))) = a x v
  simp only [ContinuousLinearEquiv.symm_apply_apply]

theorem existsUnique_smooth_cover_descent (f : M → N) (hs : Function.Surjective f)
    (hf : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (hcompat : ∀ x y, f x = f y →
      coverFiberCovector f hf n a.val x = coverFiberCovector f hf n a.val y) :
    ∃! b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F N n, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hf.contMDiff b = a := by
  have hraw := cover_raw_descent_pullback f hs hf n a.val hcompat
  let b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F N n :=
    ⟨coverRawDescent f hs hf n a.val,
      raw_form_smooth_of_cover_pullback f hs hf n _ (hraw.symm ▸ a.smooth)⟩
  have hb : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hf.contMDiff b = a := Subtype.ext hraw
  refine ⟨b, hb, ?_⟩
  intro c hc
  apply CoverPullback.CM.smooth_form_pullback_injective f hs
    (fun x => (hf.mfderivToContinuousLinearEquiv (by simp) x).surjective) hf.contMDiff n
  exact hc.trans hb.symm

end

/-! ThetaCycle: actual invariance under a smooth deck map identifies the tangent
covectors transported down a local diffeomorphism. -/

open scoped _root_.Manifold ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

theorem cover_fiber_covector_deck_invariant (f : M → N)
    (hf : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (g : M → M) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ g)
    (hfg : f ∘ g = f) (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n)
    (ha : a.pullback g = a) (x : M) :
    coverFiberCovector f hf n a x = coverFiberCovector f hf n a (g x) := by
  let J : M → E ≃L[ℝ] F := fun y => hf.mfderivToContinuousLinearEquiv (by simp) y
  have hd : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (g x)).comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x := by
    rw [← mfderiv_comp x (hf.contMDiff.mdifferentiableAt (by simp))
      (hg.mdifferentiableAt (by simp)), hfg]
  have hv (v : F) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x ((J x).symm v) = (J (g x)).symm v := by
    apply (J (g x)).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (g x)).comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x) ((J x).symm v) = v
    rw [hd]
    exact (J x).apply_symm_apply v
  ext v
  have he := congrArg (fun b : Analysis.DifferentialForms.Manifold.Basic.FormValue E n => b (fun i => (J x).symm (v i))) (congrFun ha x)
  change a (g x) (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x ((J x).symm (v i))) =
    a x (fun i => (J x).symm (v i)) at he
  simp only [hv] at he
  exact he.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverLocalM.CM
