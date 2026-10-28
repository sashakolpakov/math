import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PullbackSource
import OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorphDerivative

/-! # Pullback Immersion -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PullbackImmersion.BundleCycles

noncomputable section

section

/-! Restricting a genuine closed holomorphic immersion to the image of
a holomorphic open embedding and transporting back gives an actual closed
holomorphic immersion with injective differential. -/

open _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.OpenImmersion.Constructions.Raw
open OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorphDerivative.Constructions
open scoped _root_.Manifold ContDiff

variable {M N N' E F H : Type}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace N']
    [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E M]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F] [ChartedSpace F N]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H] [ChartedSpace H N']
    (u : M → N) (hu : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω u)
    (g : N' → N) (hg : Topology.IsOpenEmbedding g)

local notation "U" => OAI.AlgebraicGeometry.Divisors.LineBundles.HolomorphicOpenImage.BundleCycles.holomorphicOpenImage g hg
local notation "e" => OAI.AlgebraicGeometry.Divisors.LineBundles.HolomorphicOpenImage.BundleCycles.holomorphicOpenImageHomeomorph g hg

def openPullbackImmersion : CycleClass.Thom.GraphOpenImmersion.Constructions.graphSourceOpen u hu U → N' := (e).symm ∘ CycleClass.Thom.GraphOpenImmersion.Constructions.restrictedBase u hu U

variable (hga : ContMDiff 𝓘(ℂ, H) 𝓘(ℂ, F) ω g)
    (hgd : ∀ x, Function.Bijective (mfderiv 𝓘(ℂ, H) 𝓘(ℂ, F) g x))

include hga hgd in
omit [FiniteDimensional ℂ F] in
theorem openPullbackImmersion_analytic : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, H) ω (openPullbackImmersion u hu g hg) :=
  (HolomorphicOpenImage.BundleCycles.holomorphicOpenImageHomeomorph_symm_analytic g hg hga hgd).comp (CycleClass.Thom.GraphOpenImmersion.Constructions.restrictedBase_analytic u hu U)

include hga hgd in
omit [FiniteDimensional ℂ F] in
theorem openPullbackImmersion_differential
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) u x))
    (x : CycleClass.Thom.GraphOpenImmersion.Constructions.graphSourceOpen u hu U) :
    Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, H) (openPullbackImmersion u hu g hg) x) :=
  CycleClass.Thom.HolomorphicHomeomorphDerivative.Constructions.comp_mfderiv_injective (CycleClass.Thom.GraphOpenImmersion.Constructions.restrictedBase u hu U) (e).symm
    ((CycleClass.Thom.GraphOpenImmersion.Constructions.restrictedBase_analytic u hu U).mdifferentiable (by simp))
    ((HolomorphicOpenImage.BundleCycles.holomorphicOpenImageHomeomorph_symm_analytic g hg hga hgd).mdifferentiable (by simp))
    (CycleClass.Thom.OpenImmersion.Constructions.Raw.restrictedBase_differential_injective u hu U hi)
    (CycleClass.Thom.HolomorphicHomeomorphDerivative.Constructions.homeomorph_mfderiv_injective (e).symm
      ((HolomorphicOpenImage.BundleCycles.holomorphicOpenImageHomeomorph_symm_analytic g hg hga hgd).mdifferentiable (by simp))
      ((HolomorphicOpenImage.BundleCycles.holomorphicOpenImageHomeomorph_analytic g hg hga).mdifferentiable (by simp))) x

omit [FiniteDimensional ℂ F] in
theorem openPullbackImmersion_closed (hc : Topology.IsClosedEmbedding u) :
    Topology.IsClosedEmbedding (openPullbackImmersion u hu g hg) :=
  (e).symm.isClosedEmbedding.comp (CycleClass.Thom.OpenImmersion.Constructions.Raw.restrictedBase_closedEmbedding u hu U hc)

end

/-! The canonical Thom class restricts through the literal open embedding
to the Thom class of the constructed restricted immersion. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport
open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass
open scoped _root_.Manifold ContDiff

def openPullbackAmbientMap {N N' : Type} [TopologicalSpace N] [TopologicalSpace N']
    (g : N' → N) (hg : Topology.IsOpenEmbedding g) : TopCat.of N' ⟶ TopCat.of N :=
  TopCat.ofHom ⟨g, hg.continuous⟩

theorem openPullbackAmbientMap_eq {N N' : Type} [TopologicalSpace N] [TopologicalSpace N']
    (g : N' → N) (hg : Topology.IsOpenEmbedding g) :
    CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (HolomorphicOpenImage.BundleCycles.holomorphicOpenImage g hg) (HolomorphicOpenImage.BundleCycles.holomorphicOpenImageHomeomorph g hg).symm =
      openPullbackAmbientMap g hg := by
  ext x
  rfl

variable {M N N' E F H : Type}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace N']
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedSpace ℝ E]
    [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ω N] [MetrizableSpace N]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
    [ChartedSpace H N'] [IsManifold 𝓘(ℂ, H) ω N'] [MetrizableSpace N']
    (u : M → N) (hu : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω u)
    (g : N' → N) (hg : Topology.IsOpenEmbedding g)

local notation "U" => OAI.AlgebraicGeometry.Divisors.LineBundles.HolomorphicOpenImage.BundleCycles.holomorphicOpenImage g hg
local notation "e" => OAI.AlgebraicGeometry.Divisors.LineBundles.HolomorphicOpenImage.BundleCycles.holomorphicOpenImageHomeomorph g hg
local notation "w" => OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PullbackImmersion.BundleCycles.openPullbackImmersion u hu g hg

omit [FiniteDimensional ℂ E] [NormedSpace ℝ E] [IsManifold 𝓘(ℂ, E) ω M] [FiniteDimensional ℂ F] [IsManifold 𝓘(ℂ, F) ω N] [MetrizableSpace N] [MetrizableSpace N'] in
theorem openPullbackAmbientMap_mapsTo :
    Set.MapsTo (openPullbackAmbientMap g hg) (Set.range w)ᶜ (Set.range u)ᶜ :=
  CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap_mapsTo u hu U (e).symm

variable (hga : ContMDiff 𝓘(ℂ, H) 𝓘(ℂ, F) ω g)
    (hgd : ∀ x, Function.Bijective (mfderiv 𝓘(ℂ, H) 𝓘(ℂ, F) g x))
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) u x))
    (hc : Topology.IsClosedEmbedding u) (p : ℕ)

def openPullbackThomClass (hpw : CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E H = p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N') (Set.range w)ᶜ (2 * p) :=
  CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree w (openPullbackImmersion_analytic u hu g hg hga hgd)
    (openPullbackImmersion_differential u hu g hg hga hgd hi)
    (openPullbackImmersion_closed u hu g hg hc) p hpw

theorem openPullbackThomClass_from_original (hpu : CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E F = p)
    (hpw : CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E H = p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (openPullbackAmbientMap g hg)
      (openPullbackAmbientMap_mapsTo u hu g hg) (2 * p) (CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree u hu hi hc p hpu) =
      openPullbackThomClass u hu g hg hga hgd hi hc p hpw := by
  have h := CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport.ThomClass_open_ambientTransport u hu U (e).symm hi hc
    ((HolomorphicOpenImage.BundleCycles.holomorphicOpenImageHomeomorph_symm_analytic g hg hga hgd).mdifferentiable (by simp))
    ((HolomorphicOpenImage.BundleCycles.holomorphicOpenImageHomeomorph_analytic g hg hga).mdifferentiable (by simp))
    (openPullbackImmersion_analytic u hu g hg hga hgd)
    (openPullbackImmersion_differential u hu g hg hga hgd hi) p hpu hpw
  have hm := ConcreteCategory.congr_hom
    (CycleClass.Thom.ThomOpenRestriction.Constructions.pairMap_congr (openPullbackAmbientMap_eq g hg)
      (CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap_mapsTo u hu U (e).symm) (openPullbackAmbientMap_mapsTo u hu g hg) (2 * p))
    (CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree u hu hi hc p hpu)
  exact hm.symm.trans h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PullbackImmersion.BundleCycles
