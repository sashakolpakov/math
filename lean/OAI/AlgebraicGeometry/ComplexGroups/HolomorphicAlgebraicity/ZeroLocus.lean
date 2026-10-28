import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Zero Locus -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone

noncomputable section

/-!
# Local holomorphic equations for graphs and their pullbacks

These local equations use complex differentiability on open sets, the notion
available from the holomorphy hypothesis in HolomorphicAlgebraicity. Their construction requires
no multivariable power-series theorem.
-/

open Set Filter
open scoped _root_.Topology

/-- Local equations expressed using complex differentiability on an open
neighborhood. This does not assume multivariate power-series expansions. -/
def HolomorphicZeroSetAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S : Set E) (x : E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
    ∃ (m : ℕ) (f : Fin m → E → ℂ), (∀ i, DifferentiableOn ℂ (f i) U) ∧
      ∀ z ∈ U, z ∈ S ↔ ∀ i, f i z = 0

/-- A local equality of subsets transfers their holomorphic equations. -/
theorem HolomorphicZeroSetAt.congr
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {S T : Set E} {x : E} (hlocal : HolomorphicZeroSetAt S x)
    (heq : ∀ᶠ z in 𝓝 x, z ∈ T ↔ z ∈ S) : HolomorphicZeroSetAt T x := by
  obtain ⟨U, hU, hxU, m, f, hf, heqs⟩ := hlocal
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp heq
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, m, f,
    (fun i => (hf i).mono inter_subset_left), fun z hz => ?_⟩
  exact (hVsub hz.2).trans (heqs z hz.1)

/-- Pulling back finitely many local holomorphic equations keeps them
holomorphic on a suitable open neighborhood. -/
theorem HolomorphicZeroSetAt.preimage
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {S : Set F} {g : E → F} {U : Set E} {x : E}
    (hlocal : HolomorphicZeroSetAt S (g x))
    (hU : IsOpen U) (hx : x ∈ U) (hg : DifferentiableOn ℂ g U) :
    HolomorphicZeroSetAt (g ⁻¹' S) x := by
  obtain ⟨V, hV, hxV, m, f, hf, heq⟩ := hlocal
  refine ⟨U ∩ g ⁻¹' V, hg.continuousOn.isOpen_inter_preimage hU hV,
    ⟨hx, hxV⟩, m, (fun i z => f i (g z)), (fun i => ?_), ?_⟩
  · exact (hf i).comp (hg.mono inter_subset_left) (fun z hz => hz.2)
  · intro z hz
    exact heq (g z) hz.2

/-- The graph of a holomorphic map to a coordinate space has explicit local
equations: the difference of its target coordinates and the map's values. -/
theorem holomorphicZeroSetAt_graph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {m : ℕ} {f : E → (Fin m → ℂ)} {U : Set E}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : E} (hx : x ∈ U) :
    HolomorphicZeroSetAt {p : E × (Fin m → ℂ) | p.2 = f p.1} (x, f x) := by
  have hfst : Differentiable ℂ (Prod.fst : E × (Fin m → ℂ) → E) := differentiable_fst
  have hsnd : Differentiable ℂ (Prod.snd : E × (Fin m → ℂ) → (Fin m → ℂ)) :=
    differentiable_snd
  have heval (i : Fin m) : Differentiable ℂ (fun z : Fin m → ℂ => z i) :=
    differentiable_apply i
  refine ⟨Prod.fst ⁻¹' U, hU.preimage continuous_fst, hx, m,
    (fun i p => p.2 i - f p.1 i), (fun i => ?_), ?_⟩
  · apply DifferentiableOn.sub
    · exact ((heval i).comp hsnd).differentiableOn
    · exact (heval i).comp_differentiableOn
        (hf.comp hfst.differentiableOn (mapsTo_preimage Prod.fst U))
  · intro p _
    simp only [mem_ofPred_eq, sub_eq_zero]
    exact funext_iff

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone
