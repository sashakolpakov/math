import OAI.AlgebraicGeometry.Divisors.LineBundles.HolomorphicOpenImage
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement

/-! # Pullback Source -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PullbackSource.BundleCycles

noncomputable section

/-! An actual open pullback of an immersion parametrizes precisely the
source of the restricted immersion. The parametrization is constructed
from the image equality and is surjective by injectivity of the immersion. -/

open _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions
open scoped _root_.Manifold ContDiff

variable {M M' N N' E F : Type}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace N']
    [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E M]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace F N]
    (u : M → N) (hu : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω u)
    (g : N' → N) (hg : Topology.IsOpenEmbedding g) (v : M' → N')
    (himage : Set.range v = g ⁻¹' Set.range u)

local notation "U" => OAI.AlgebraicGeometry.Divisors.LineBundles.HolomorphicOpenImage.BundleCycles.holomorphicOpenImage g hg
local notation "e" => OAI.AlgebraicGeometry.Divisors.LineBundles.HolomorphicOpenImage.BundleCycles.holomorphicOpenImageHomeomorph g hg

include himage in
omit [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace N'] in
theorem openPullbackSource_exists (x : M') : ∃ m, u m = g (v x) :=
  (Set.ext_iff.mp himage (v x)).mp (Set.mem_range_self x)

def openPullbackSourceLift (x : M') : CycleClass.Thom.GraphOpenImmersion.Constructions.graphSourceOpen u hu U :=
  ⟨Classical.choose (openPullbackSource_exists u g v himage x), by
    change u (Classical.choose (openPullbackSource_exists u g v himage x)) ∈ Set.range g
    rw [Classical.choose_spec (openPullbackSource_exists u g v himage x)]
    exact Set.mem_range_self (v x)⟩

theorem openPullbackSourceLift_value (x : M') :
    u (openPullbackSourceLift u hu g hg v himage x).val = g (v x) :=
  Classical.choose_spec (openPullbackSource_exists u g v himage x)

theorem openPullbackSourceLift_surjective (hi : Function.Injective u) :
    Function.Surjective (openPullbackSourceLift u hu g hg v himage) := by
  intro z
  obtain ⟨y, hy⟩ := z.property
  have hgy : g y ∈ Set.range u := ⟨z.val, hy.symm⟩
  obtain ⟨x, hx⟩ := (Set.ext_iff.mp himage y).mpr hgy
  refine ⟨x, Subtype.ext (hi ?_)⟩
  exact (openPullbackSourceLift_value u hu g hg v himage x).trans ((congrArg g hx).trans hy)

theorem openPullbackSourceLift_commutes :
    (e).symm ∘ CycleClass.Thom.GraphOpenImmersion.Constructions.restrictedBase u hu U ∘ openPullbackSourceLift u hu g hg v himage = v := by
  funext x
  apply (e).injective
  change (e) ((e).symm (CycleClass.Thom.GraphOpenImmersion.Constructions.restrictedBase u hu U (openPullbackSourceLift u hu g hg v himage x))) = (e) (v x)
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  exact openPullbackSourceLift_value u hu g hg v himage x

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PullbackSource.BundleCycles
