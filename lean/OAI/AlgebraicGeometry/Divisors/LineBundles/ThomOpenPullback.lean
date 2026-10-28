import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PullbackImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.CommutingSquare

/-! # Thom Open Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ThomOpenPullback.BundleCycles

noncomputable section

/-! The canonical Thom class pulls back through an actual holomorphic
open embedding. The source parametrization is constructed from the
cartesian image equality; no cohomological comparison is assumed. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.CommutingSquare.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TransportRestriction.Constructions
open scoped _root_.Manifold ContDiff

theorem openPullbackThom_mapsTo {M M' N N' : Type}
    [TopologicalSpace N] [TopologicalSpace N'] (u : M → N) (g : N' → N)
    (hg : Topology.IsOpenEmbedding g) (v : M' → N')
    (himage : Set.range v = g ⁻¹' Set.range u) :
    Set.MapsTo (Open.PullbackImmersion.BundleCycles.openPullbackAmbientMap g hg) (Set.range v)ᶜ (Set.range u)ᶜ := by
  intro x hx hu
  exact hx ((Set.ext_iff.mp himage x).mpr hu)

variable {M M' N N' E E' F H : Type}
    [TopologicalSpace M] [TopologicalSpace M'] [TopologicalSpace N] [TopologicalSpace N']
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedSpace ℝ E]
    [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E'] [NormedSpace ℝ E']
    [ChartedSpace E' M'] [IsManifold 𝓘(ℂ, E') ω M']
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ω N] [MetrizableSpace N]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
    [ChartedSpace H N'] [IsManifold 𝓘(ℂ, H) ω N'] [MetrizableSpace N']
    (u : M → N) (hu : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω u)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) u x))
    (hc : Topology.IsClosedEmbedding u)
    (g : N' → N) (hg : Topology.IsOpenEmbedding g)
    (hga : ContMDiff 𝓘(ℂ, H) 𝓘(ℂ, F) ω g)
    (hgd : ∀ x, Function.Bijective (mfderiv 𝓘(ℂ, H) 𝓘(ℂ, F) g x))
    (v : M' → N') (hv : ContMDiff 𝓘(ℂ, E') 𝓘(ℂ, H) ω v)
    (hvi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E') 𝓘(ℂ, H) v x))
    (hvc : Topology.IsClosedEmbedding v)
    (himage : Set.range v = g ⁻¹' Set.range u)
    (l : E ≃L[ℂ] E') (hl : ∀ z, ‖l z‖ = ‖z‖)

include hga hgd l hl in
theorem complexThomClassInDegree_openPullback (p : ℕ)
    (hpu : CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E F = p)
    (hpw : CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E H = p)
    (hpv : CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E' H = p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Open.PullbackImmersion.BundleCycles.openPullbackAmbientMap g hg)
      (openPullbackThom_mapsTo u g hg v himage) (2 * p)
      (CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree u hu hi hc p hpu) =
      CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree v hv hvi hvc p hpv := by
  let w := Open.PullbackImmersion.BundleCycles.openPullbackImmersion u hu g hg
  let a := Open.PullbackSource.BundleCycles.openPullbackSourceLift u hu g hg v himage
  have ha : Function.Surjective a := Open.PullbackSource.BundleCycles.openPullbackSourceLift_surjective u hu g hg v himage hc.injective
  have hcomm : (Homeomorph.refl N') ∘ v = w ∘ a :=
    (Open.PullbackSource.BundleCycles.openPullbackSourceLift_commutes u hu g hg v himage).symm
  have hwa := Open.PullbackImmersion.BundleCycles.openPullbackImmersion_analytic u hu g hg hga hgd
  have hwi := Open.PullbackImmersion.BundleCycles.openPullbackImmersion_differential u hu g hg hga hgd hi
  have hwc := Open.PullbackImmersion.BundleCycles.openPullbackImmersion_closed u hu g hg hc
  have he : ContMDiff 𝓘(ℂ, H) 𝓘(ℂ, H) ω (Homeomorph.refl N') := contMDiff_id
  have hei : MDifferentiable 𝓘(ℂ, H) 𝓘(ℂ, H) (Homeomorph.refl N').symm := mdifferentiable_id
  have hcompare := CycleClass.Thom.CommutingSquare.Constructions.complexThomClassInDegree_commutingSquare v hv hvi hvc w hwa hwi hwc
    (Homeomorph.refl N') he hei a ha hcomm l hl p hpv hpw hpv
  let k := CycleClass.Thom.NormalPair.TransportRestriction.Constructions.ambientTransportMap (Homeomorph.refl N')
  have hk : Set.MapsTo k (Set.range v)ᶜ (Set.range w)ᶜ :=
    CycleClass.Thom.CommutingSquare.Constructions.squareMapsTo v w (Homeomorph.refl N') a ha hcomm
  have hw := Open.PullbackImmersion.BundleCycles.openPullbackAmbientMap_mapsTo u hu g hg
  have h₁ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) k (Open.PullbackImmersion.BundleCycles.openPullbackAmbientMap g hg)
      hk hw (2 * p)) (CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree u hu hi hc p hpu)
  have hmap : k ≫ Open.PullbackImmersion.BundleCycles.openPullbackAmbientMap g hg = Open.PullbackImmersion.BundleCycles.openPullbackAmbientMap g hg := by
    ext x
    rfl
  have h₂ := ConcreteCategory.congr_hom
    (CycleClass.Thom.ThomOpenRestriction.Constructions.pairMap_congr hmap (hw.comp hk)
      (openPullbackThom_mapsTo u g hg v himage) (2 * p))
    (CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree u hu hi hc p hpu)
  have h₃ := congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) k hk (2 * p))
    (Open.PullbackImmersion.BundleCycles.openPullbackThomClass_from_original u hu g hg hga hgd hi hc p hpu hpw)
  exact h₂.symm.trans (h₁.symm.trans (h₃.trans hcompare))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ThomOpenPullback.BundleCycles
