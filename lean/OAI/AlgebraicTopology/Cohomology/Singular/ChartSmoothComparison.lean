import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothModels
import OAI.AlgebraicTopology.Cohomology.Singular.SmoothConvexComparison
import OAI.AlgebraicTopology.Cohomology.Singular.ChartBalls
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Algebra.Homology.QuasiIso

/-! # Chart Smooth Comparison -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ChartSmoothComparison

noncomputable section

/-!
# Smooth singular comparison in chart neighborhoods

Actual smooth diffeomorphisms induce compatible isomorphisms of continuous and
smooth singular cochains. These preserve the genuine smooth-simplex restriction
map, allowing the proved convex-domain comparison to be transported to chart
neighborhoods. No global smoothing theorem or de Rham comparison is assumed.
-/

open _root_.CategoryTheory Opposite
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {E F : Type}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {M N : Type}
variable [TopologicalSpace M] [ChartedSpace E M]
variable [TopologicalSpace N] [ChartedSpace F N]

/-- A smooth diffeomorphism gives an isomorphism of the actual smooth singular
simplicial sets. -/
def manifoldSmoothSingularDiffeomorphIso
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞) :
    (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet ≅
      (ManifoldSmooth.manifoldSmoothSingularSubcomplex F N).toSSet where
  hom := ManifoldSmoothFunctor.manifoldSmoothSingularMap E F e e.contMDiff
  inv := ManifoldSmoothFunctor.manifoldSmoothSingularMap F E e.symm e.symm.contMDiff
  hom_inv_id := by
    ext n σ
    apply Subtype.ext
    apply ((TopCat.of M).toSSetObjEquiv n).injective
    ext x
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext n σ
    apply Subtype.ext
    apply ((TopCat.of N).toSSetObjEquiv n).injective
    ext x
    exact e.apply_symm_apply _

variable {R : Type} [Ring R]

/-- Contravariant transport of genuine smooth cochains by a diffeomorphism. -/
def manifoldSmoothCochainsDiffeomorphIso (A : ModuleCat.{0} R)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞) :
    ManifoldSmooth.manifoldSmoothCochains F A N ≅ ManifoldSmooth.manifoldSmoothCochains E A M :=
  (Functor.simplicialCochainsFunctor A).mapIso (manifoldSmoothSingularDiffeomorphIso e).op

/-- Contravariant transport of continuous singular cochains by the underlying
homeomorphism of an actual diffeomorphism. -/
def continuousCochainsDiffeomorphIso (A : ModuleCat.{0} R)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞) :
    Basic.singularCochains A (TopCat.of N) ≅ Basic.singularCochains A (TopCat.of M) :=
  (Functor.singularCochainsFunctor A).mapIso (TopCat.isoOfHomeo e.toHomeomorph).op

/-- The continuous-to-smooth restriction maps form an isomorphic arrow under
an actual diffeomorphism. -/
def manifoldSmoothRestrictionDiffeomorphArrowIso (A : ModuleCat.{0} R)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞) :
    Arrow.mk (ManifoldSmooth.manifoldSmoothCochainRestriction F A N) ≅
      Arrow.mk (ManifoldSmooth.manifoldSmoothCochainRestriction E A M) :=
  Arrow.isoMk (continuousCochainsDiffeomorphIso A e)
    (manifoldSmoothCochainsDiffeomorphIso A e)
    (ManifoldSmoothFunctor.manifoldSmoothCochainRestriction_naturality A e e.contMDiff)

/-- The genuine smooth-cochain comparison is invariant under diffeomorphism. -/
theorem quasiIso_manifoldSmoothRestriction_diffeomorph_iff (A : ModuleCat.{0} R)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞) :
    QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction F A N) ↔
      QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction E A M) :=
  quasiIso_iff_of_arrow_mk_iso _ _
    (manifoldSmoothRestrictionDiffeomorphArrowIso A e)

/-- On an actual nonempty convex open subset of a normed space, the manifold
smooth cochains agree with the previously verified convex-domain model. -/
theorem quasiIso_convexManifoldSmoothRestriction (A : ModuleCat.{0} R)
    (U : TopologicalSpace.Opens F) (hU : Convex ℝ (U : Set F))
    (hne : (U : Set F).Nonempty) :
    QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction F A U) := by
  have : QuasiIso (SmoothOpen.subsetSmoothCochainRestriction A (U : Set F)) := by
    refine ⟨fun n => ?_⟩
    exact (quasiIsoAt_iff_isIso_homologyMap _ n).2
      (SmoothConvexComparison.isIso_convexSmoothCohomologyRestriction A hU hne n)
  have : QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction F A U ≫
      (ManifoldSmoothModels.manifoldSmoothOpenCochainsIso F U A).hom) := by
    rw [ManifoldSmoothModels.manifoldSmoothOpenCochainRestriction_iso_hom]
    infer_instance
  exact quasiIso_of_comp_right (ManifoldSmooth.manifoldSmoothCochainRestriction F A U)
    (ManifoldSmoothModels.manifoldSmoothOpenCochainsIso F U A).hom

/-- Transport the actual convex comparison through a verified smooth
diffeomorphism to a convex open subset of a normed model space. -/
theorem quasiIso_manifoldSmoothRestriction_of_convexDiffeomorph (A : ModuleCat.{0} R)
    (U : TopologicalSpace.Opens F) (hU : Convex ℝ (U : Set F))
    (hne : (U : Set F).Nonempty)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M U ∞) :
    QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction E A M) :=
  (quasiIso_manifoldSmoothRestriction_diffeomorph_iff A e).mp
    (quasiIso_convexManifoldSmoothRestriction A U hU hne)

/-- The actual cohomology comparison on a manifold diffeomorphic to a convex
open domain. Its forward map is the smooth-simplex restriction. -/
def convexDiffeomorphSmoothCohomologyIso (A : ModuleCat.{0} R)
    (U : TopologicalSpace.Opens F) (hU : Convex ℝ (U : Set F))
    (hne : (U : Set F).Nonempty)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M U ∞) (n : ℕ) :
    Basic.singularCohomology A (TopCat.of M) n ≅ (ManifoldSmooth.manifoldSmoothCochains E A M).homology n := by
  letI := quasiIso_manifoldSmoothRestriction_of_convexDiffeomorph A U hU hne e
  exact isoOfQuasiIsoAt (ManifoldSmooth.manifoldSmoothCochainRestriction E A M) n

@[simp]
theorem convexDiffeomorphSmoothCohomologyIso_hom (A : ModuleCat.{0} R)
    (U : TopologicalSpace.Opens F) (hU : Convex ℝ (U : Set F))
    (hne : (U : Set F).Nonempty)
    (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M U ∞) (n : ℕ) :
    (convexDiffeomorphSmoothCohomologyIso A U hU hne e n).hom =
      HomologicalComplex.homologyMap (ManifoldSmooth.manifoldSmoothCochainRestriction E A M) n := rfl

variable (E) in
/-- The target model ball as an open submanifold of the normed model space. -/
def chartBallModelOpen (x : M) (r : ℝ) : TopologicalSpace.Opens E :=
  ⟨Metric.ball (chartAt E x x) r, Metric.isOpen_ball⟩

variable [IsManifold 𝓘(ℝ, E) ∞ M]

variable (E) in
/-- The actual chart homeomorphism on an admissible chart ball has smooth
forward and inverse maps in the inherited open-submanifold structures. -/
def chartBallDiffeomorph (x : M) (r : ℝ)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E)
      (ChartBalls.chartBallOpen E x r) (chartBallModelOpen E x r) ∞ where
  toEquiv := (ChartBalls.chartBallHomeomorph E x r htarget).toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (chartBallModelOpen E x r) _).mp
    intro y
    change ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun z : ChartBalls.chartBallOpen E x r => chartAt E x (z : M)) y
    apply contMDiffAt_subtype_iff.mpr
    exact contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞) x) y.property.1
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (ChartBalls.chartBallOpen E x r) _).mp
    intro y
    change ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun z : chartBallModelOpen E x r => (chartAt E x).symm (z : E)) y
    apply contMDiffAt_subtype_iff.mpr
    exact contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞) x)
      (htarget y.property)

@[simp]
theorem chartBallDiffeomorph_apply (x : M) (r : ℝ)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target)
    (y : ChartBalls.chartBallOpen E x r) :
    (chartBallDiffeomorph E x r htarget y : E) = chartAt E x y := rfl

@[simp]
theorem chartBallDiffeomorph_symm_apply (x : M) (r : ℝ)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target)
    (y : chartBallModelOpen E x r) :
    ((chartBallDiffeomorph E x r htarget).symm y : M) = (chartAt E x).symm y := rfl

variable (E) in
/-- The actual continuous-to-smooth cochain restriction on an admissible
positive-radius chart ball is a quasi-isomorphism. -/
theorem quasiIso_chartBallSmoothRestriction (A : ModuleCat.{0} R)
    (x : M) (r : ℝ) (hr : 0 < r)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target) :
    QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction E A (ChartBalls.chartBallOpen E x r)) :=
  quasiIso_manifoldSmoothRestriction_of_convexDiffeomorph A
    (chartBallModelOpen E x r) (convex_ball (chartAt E x x) r)
    ⟨chartAt E x x, Metric.mem_ball_self hr⟩ (chartBallDiffeomorph E x r htarget)

variable (E) in
/-- The cohomology isomorphism on a genuine chart-ball domain, induced by
restriction of ordinary singular cochains to manifold-smooth simplices. -/
def chartBallSmoothCohomologyIso (A : ModuleCat.{0} R)
    (x : M) (r : ℝ) (hr : 0 < r)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target) (n : ℕ) :
    Basic.singularCohomology A (TopCat.of (ChartBalls.chartBallOpen E x r)) n ≅
      (ManifoldSmooth.manifoldSmoothCochains E A (ChartBalls.chartBallOpen E x r)).homology n := by
  letI := quasiIso_chartBallSmoothRestriction E A x r hr htarget
  exact isoOfQuasiIsoAt (ManifoldSmooth.manifoldSmoothCochainRestriction E A (ChartBalls.chartBallOpen E x r)) n

@[simp]
theorem chartBallSmoothCohomologyIso_hom (A : ModuleCat.{0} R)
    (x : M) (r : ℝ) (hr : 0 < r)
    (htarget : Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target) (n : ℕ) :
    (chartBallSmoothCohomologyIso E A x r hr htarget n).hom =
      HomologicalComplex.homologyMap
        (ManifoldSmooth.manifoldSmoothCochainRestriction E A (ChartBalls.chartBallOpen E x r)) n := rfl

variable (E) in
/-- Every neighborhood contains an actual open neighborhood on which smooth
singular restriction is a quasi-isomorphism. -/
theorem exists_open_smoothComparison_subset (A : ModuleCat.{0} R)
    (x : M) {s : Set M} (hs : s ∈ 𝓝 x) :
    ∃ U : TopologicalSpace.Opens M, x ∈ U ∧ (U : Set M) ⊆ s ∧
      QuasiIso (ManifoldSmooth.manifoldSmoothCochainRestriction E A U) := by
  obtain ⟨r, hr, ht, hsub⟩ := ChartBalls.exists_chartBall_subset_of_mem_nhds E x hs
  exact ⟨ChartBalls.chartBallOpen E x r, ChartBalls.mem_chartBallDomain_self E x hr, hsub,
    quasiIso_chartBallSmoothRestriction E A x r hr ht⟩

end

end OAI.AlgebraicTopology.Cohomology.Singular.ChartSmoothComparison
