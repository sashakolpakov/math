import OAI.RepresentationTheory.Theta.Geometric.Geometry
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-! # Theta At -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! The differential of the rational action on the actual open ball is
its original Frechet derivative in the ball coordinates. -/

set_option backward.isDefEq.respectTransparency false
open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

theorem Period.ThetaAt.openSubtype_mfderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (U : Opens V) (x : U) :
    mfderiv 𝓘(ℂ, V) 𝓘(ℂ, V) (Subtype.val : U → V) x = ContinuousLinearMap.id ℂ V := by
  exact mfderiv_extChartAt_self

theorem Period.ThetaAt.openRestrict_mfderiv {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (U : Opens V) (f : V → W) (x : U) (hf : DifferentiableAt ℂ f x.val) :
    mfderiv 𝓘(ℂ, V) 𝓘(ℂ, W) (fun y : U => f y.val) x = fderiv ℂ f x.val := by
  have hsub : MDifferentiableAt 𝓘(ℂ, V) 𝓘(ℂ, V) (Subtype.val : U → V) x :=
    (contMDiff_subtype_val (I := 𝓘(ℂ, V)) (n := ∞)).mdifferentiable (by simp) x
  have h := mfderiv_comp x hf.mdifferentiableAt hsub
  exact h.trans ((congrArg₂ (fun (a : V →L[ℂ] W) (b : V →L[ℂ] V) => a.comp b)
    (mfderiv_eq_fderiv (𝕜 := ℂ) (f := f) (x := x.val)) (Period.ThetaAt.openSubtype_mfderiv U x)).trans
      (ContinuousLinearMap.comp_id _))

theorem Period.ThetaAt.openCodomain_mdifferentiableAt_iff {V W M N : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    [TopologicalSpace M] [ChartedSpace V M] [TopologicalSpace N] [ChartedSpace W N]
    (U : Opens N) (f : M → U) (x : M) :
    MDifferentiableAt 𝓘(ℂ, V) 𝓘(ℂ, W) (Subtype.val ∘ f) x ↔
      MDifferentiableAt 𝓘(ℂ, V) 𝓘(ℂ, W) f x := by
  simp only [MDifferentiableAt, ChartedSpace.LiftPropAt,
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff]

theorem Period.ThetaAt.openCodomain_mfderiv {V W M N : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    [TopologicalSpace M] [ChartedSpace V M] [TopologicalSpace N] [ChartedSpace W N]
    (U : Opens N) (f : M → U) (x : M) :
    (show V →L[ℂ] W from mfderiv 𝓘(ℂ, V) 𝓘(ℂ, W) f x) =
      (show V →L[ℂ] W from mfderiv 𝓘(ℂ, V) 𝓘(ℂ, W) (Subtype.val ∘ f) x) := by
  unfold mfderiv
  rw [← Period.ThetaAt.openCodomain_mdifferentiableAt_iff U f x]
  rfl

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def Data.ActiveHeckeThetaData.periodDomainMap (g : D.RationalSU) : D.domain → D.domain :=
  fun x => ⟨D.periodMap g x.val, D.periodMap_preserves g x.val x.property⟩

theorem Data.ActiveHeckeThetaData.periodDomainMap_mdifferentiable (g : D.RationalSU) :
    MDifferentiable 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, LinearTheta.BallCoordinates) (D.periodDomainMap g) := by
  intro x
  apply (Period.ThetaAt.openCodomain_mdifferentiableAt_iff D.domain (D.periodDomainMap g) x).mp
  exact (D.periodMap_differentiableAt g x).mdifferentiableAt.comp x
    ((contMDiff_subtype_val (I := 𝓘(ℂ, LinearTheta.BallCoordinates)) (n := ∞)).mdifferentiable (by simp) x)

theorem Data.ActiveHeckeThetaData.periodDomainMap_mfderiv (g : D.RationalSU) (x : D.domain) :
    mfderiv 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, LinearTheta.BallCoordinates) (D.periodDomainMap g) x =
      fderiv ℂ (D.periodMap g) x.val := by
  exact (Period.ThetaAt.openCodomain_mfderiv D.domain (D.periodDomainMap g) x).trans
    (Period.ThetaAt.openRestrict_mfderiv D.domain (D.periodMap g) x (D.periodMap_differentiableAt g x))

end

section

/-! Rational automorphy and the actual period differential give a
well-defined complex covector at each point of the period quotient.
Its pullback is the original theta covector, independently of the lift. -/

set_option backward.isDefEq.respectTransparency false
open scoped _root_.Manifold ContDiff

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (cover : D.domain → X.analyticSpace)
    (hcover : D.IsPeriodUniformization X cover)

def Data.ActiveHeckeThetaData.periodTangentEquiv (x : D.domain) : LinearTheta.BallCoordinates ≃L[ℂ] X.analyticModel := by
  let f : LinearTheta.BallCoordinates →L[ℂ] X.analyticModel :=
    mfderiv 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, X.analyticModel) cover x
  let e : LinearTheta.BallCoordinates ≃ₗ[ℂ] X.analyticModel :=
    LinearEquiv.ofBijective f.toLinearMap (hcover.2.2.2.1 x)
  exact e.toContinuousLinearEquiv

include hcover

theorem Data.ActiveHeckeThetaData.periodTangentEquiv_apply (x : D.domain) (u : LinearTheta.BallCoordinates) :
    D.periodTangentEquiv X cover hcover x u =
      mfderiv 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, X.analyticModel) cover x u := rfl

theorem Data.ActiveHeckeThetaData.periodCover_invariant (g : D.RationalSU)
    (hg : D.rationalFinite g ∈ (SphericalGU.Spherical.integralSL3 q).prod D.awayLevel.toSubgroup) :
    cover ∘ D.periodDomainMap g = cover := by
  funext x
  exact ((hcover.2.2.2.2 x (D.periodDomainMap g x)).mpr ⟨g, hg, rfl⟩).symm

theorem Data.ActiveHeckeThetaData.periodCover_mfderiv_invariant (g : D.RationalSU)
    (hg : D.rationalFinite g ∈ (SphericalGU.Spherical.integralSL3 q).prod D.awayLevel.toSubgroup)
    (x : D.domain) (u : LinearTheta.BallCoordinates) :
    mfderiv 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, X.analyticModel) cover (D.periodDomainMap g x)
        (fderiv ℂ (D.periodMap g) x.val u) =
      mfderiv 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, X.analyticModel) cover x u := by
  have h := mfderiv_comp x (hcover.2.2.1 (D.periodDomainMap g x))
    (D.periodDomainMap_mdifferentiable g x)
  have hv := congrArg (fun a : LinearTheta.BallCoordinates →L[ℂ] X.analyticModel => a u) h
  have hg' := congrArg (fun a : LinearTheta.BallCoordinates →L[ℂ] LinearTheta.BallCoordinates => a u)
    (D.periodDomainMap_mfderiv g x)
  have hc := congrArg
    (fun f : D.domain → X.analyticSpace =>
      mfderiv 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, X.analyticModel) f x u)
    (D.periodCover_invariant X cover hcover g hg)
  exact (congrArg
    (mfderiv 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, X.analyticModel) cover (D.periodDomainMap g x))
    hg'.symm).trans (hv.symm.trans hc)

def Data.ActiveHeckeThetaData.transportedThetaCovector (φ : D.sphericalInputs) (x : D.domain) :
    X.analyticModel →L[ℂ] ℂ :=
  (D.thetaUniversal φ.val x.val).comp
    (D.periodTangentEquiv X cover hcover x).symm.toContinuousLinearMap

theorem Data.ActiveHeckeThetaData.transportedThetaCovector_pullback (φ : D.sphericalInputs) (x : D.domain)
    (u : LinearTheta.BallCoordinates) :
    D.transportedThetaCovector X cover hcover φ x
      (mfderiv 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, X.analyticModel) cover x u) =
        D.thetaUniversal φ.val x.val u := by
  change D.thetaUniversal φ.val x.val
    ((D.periodTangentEquiv X cover hcover x).symm (D.periodTangentEquiv X cover hcover x u)) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

theorem Data.ActiveHeckeThetaData.transportedThetaCovector_invariant (ha : D.HasRationalThetaCovariance)
    (φ : D.sphericalInputs) (g : D.RationalSU)
    (hg : D.rationalFinite g ∈ (SphericalGU.Spherical.integralSL3 q).prod D.awayLevel.toSubgroup)
    (x : D.domain) :
    D.transportedThetaCovector X cover hcover φ (D.periodDomainMap g x) =
      D.transportedThetaCovector X cover hcover φ x := by
  ext v
  obtain ⟨u, rfl⟩ := (hcover.2.2.2.1 x).surjective v
  rw [← D.periodCover_mfderiv_invariant X cover hcover g hg x u,
    D.transportedThetaCovector_pullback]
  rw [D.periodCover_mfderiv_invariant X cover hcover g hg x u,
    D.transportedThetaCovector_pullback]
  have h := ha g φ.val x
  rw [φ.property (D.rationalFinite g) hg] at h
  exact congrArg (fun a : LinearTheta.Cotangent => a u) h

theorem Data.ActiveHeckeThetaData.transportedThetaCovector_fiber (ha : D.HasRationalThetaCovariance)
    (φ : D.sphericalInputs) (x y : D.domain) (hxy : cover x = cover y) :
    D.transportedThetaCovector X cover hcover φ x =
      D.transportedThetaCovector X cover hcover φ y := by
  obtain ⟨g, hg, hgy⟩ := (hcover.2.2.2.2 x y).mp hxy
  have hy : y = D.periodDomainMap g x := Subtype.ext hgy
  exact (D.transportedThetaCovector_invariant X cover hcover ha φ g hg x).symm.trans
    (congrArg (D.transportedThetaCovector X cover hcover φ) hy.symm)

def Data.ActiveHeckeThetaData.periodThetaCovector (φ : D.sphericalInputs) (y : X.analyticSpace) :
    X.analyticModel →L[ℂ] ℂ :=
  D.transportedThetaCovector X cover hcover φ (hcover.1 y).choose

theorem Data.ActiveHeckeThetaData.periodThetaCovector_at_cover (ha : D.HasRationalThetaCovariance)
    (φ : D.sphericalInputs) (x : D.domain) :
    D.periodThetaCovector X cover hcover φ (cover x) =
      D.transportedThetaCovector X cover hcover φ x :=
  D.transportedThetaCovector_fiber X cover hcover ha φ _ x (hcover.1 (cover x)).choose_spec

theorem Data.ActiveHeckeThetaData.periodThetaCovector_pullback (ha : D.HasRationalThetaCovariance)
    (φ : D.sphericalInputs) (x : D.domain) (u : LinearTheta.BallCoordinates) :
    D.periodThetaCovector X cover hcover φ (cover x)
      (mfderiv 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, X.analyticModel) cover x u) =
        D.thetaUniversal φ.val x.val u := by
  rw [D.periodThetaCovector_at_cover X cover hcover ha φ x]
  exact D.transportedThetaCovector_pullback X cover hcover φ x u

end

/-! The actual descended covectors depend complex-linearly on the
spherical input and are uniquely determined by their period pullback. -/

set_option backward.isDefEq.respectTransparency false
open scoped _root_.Manifold ContDiff

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (cover : D.domain → X.analyticSpace)
    (hcover : D.IsPeriodUniformization X cover)

def Data.ActiveHeckeThetaData.periodThetaCovectorLinear :
    D.sphericalInputs →ₗ[ℂ] (X.analyticSpace → X.analyticModel →L[ℂ] ℂ) where
  toFun := D.periodThetaCovector X cover hcover
  map_add' φ ψ := by
    funext y
    ext v
    change D.thetaUniversal (φ + ψ).val _ _ = D.thetaUniversal φ.val _ _ + D.thetaUniversal ψ.val _ _
    simp only [Submodule.coe_add, map_add, Pi.add_apply]
    rfl
  map_smul' a φ := by
    funext y
    ext v
    change D.thetaUniversal (a • φ).val _ _ = a • D.thetaUniversal φ.val _ _
    simp only [Submodule.coe_smul, map_smul, Pi.smul_apply]
    rfl

theorem Data.ActiveHeckeThetaData.periodThetaCovector_unique (ha : D.HasRationalThetaCovariance)
    (φ : D.sphericalInputs) (c : X.analyticSpace → X.analyticModel →L[ℂ] ℂ)
    (hc : ∀ (x : D.domain) (u : LinearTheta.BallCoordinates), c (cover x)
      (mfderiv 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, X.analyticModel) cover x u) =
        D.thetaUniversal φ.val x.val u) :
    c = D.periodThetaCovector X cover hcover φ := by
  funext y
  obtain ⟨x, rfl⟩ := hcover.1 y
  ext v
  obtain ⟨u, rfl⟩ := (hcover.2.2.2.1 x).surjective v
  exact (hc x u).trans (D.periodThetaCovector_pullback X cover hcover ha φ x u).symm

include hcover in
theorem Data.ActiveHeckeThetaData.periodUniformization_dimension (x : D.domain) : X.complexDimension = 2 := by
  have h := (D.periodTangentEquiv X cover hcover x).toLinearEquiv.finrank_eq
  rw [X.analyticModel_complex_finrank] at h
  have hb : Module.finrank ℂ LinearTheta.BallCoordinates = 2 := by
    change Module.finrank ℂ (Fin 2 → ℂ) = 2
    exact Module.finrank_fin_fun ℂ
  exact h.symm.trans hb

end

end OAI.RepresentationTheory.Theta.Geometric
