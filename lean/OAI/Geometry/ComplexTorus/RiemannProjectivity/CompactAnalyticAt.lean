import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProperAnalyticImage
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AnalyticFibers
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Compact Analytic At -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.CompactAnalyticAt.Constructions.CompactAnalytic

noncomputable section

/-!
# RiemannProjectivity: compact analytic subsets of affine space are finite

Coordinate fibers are compact analytic subsets of a complex line. Their
finiteness permits proper analytic elimination of one coordinate. Induction
on the ambient dimension then proves finiteness of the whole compact set.
-/

open Set Filter _root_.Metric
open scoped _root_.Topology

theorem lineAnalyticAt_of_holomorphic {S : Set ℂ} {x : ℂ}
    (h : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S x) : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AnalyticFibers.Constructions.Cone.LineAnalyticAt S x := by
  obtain ⟨U, hU, hx, m, f, hf, heq⟩ := h
  exact ⟨m, f, fun i => (hf i).analyticAt (hU.mem_nhds hx),
    mem_of_superset (hU.mem_nhds hx) (fun y hy => heq y hy)⟩

theorem finite_vertical_fiber {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {S : Set (V × ℂ)} (hS : IsCompact S)
    (hlocal : ∀ p ∈ S, AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S p) (x : V) :
    {z : ℂ | (x, z) ∈ S}.Finite := by
  have hcompact : IsCompact {z : ℂ | (x, z) ∈ S} := by
    have h := (hS.inter_right ((isClosed_singleton (x := x)).preimage
      (continuous_fst : Continuous (Prod.fst : V × ℂ → V)))).image continuous_snd
    convert! h using 1
    ext z
    simp only [mem_ofPred_eq, mem_image, mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · intro hz
      exact ⟨(x, z), ⟨hz, rfl⟩, rfl⟩
    · rintro ⟨⟨y, w⟩, ⟨hp, rfl⟩, rfl⟩
      exact hp
  apply AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AnalyticFibers.Constructions.Cone.finite_of_isCompact_lineAnalytic hcompact
  intro z hz
  apply lineAnalyticAt_of_holomorphic
  exact (hlocal (x, z) hz).preimage isOpen_univ (mem_univ z)
    ((differentiable_const x).prodMk differentiable_id).differentiableOn

theorem compact_projection_holomorphic {n : ℕ} {S : Set ((Fin n → ℂ) × ℂ)}
    (hS : IsCompact S) (hlocal : ∀ p ∈ S, AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S p)
    (x : Fin n → ℂ) : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (Prod.fst '' S) x := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have h := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProperAnalyticImage.Constructions.Cone.holomorphicZeroSetAt_proper_projection
    (continuous_fst.comp continuous_subtype_val).isProperMap
    (finite_vertical_fiber hS hlocal x) (fun z hz => hlocal (x, z) hz)
  have heq : {y | ∃ z, (y, z) ∈ S} = Prod.fst '' S := by
    ext y
    exact ⟨fun ⟨z, hz⟩ => ⟨(y, z), hz, rfl⟩,
      fun ⟨⟨w, z⟩, hp, he⟩ => ⟨z, he ▸ hp⟩⟩
  rwa [heq] at h

theorem finite_of_isCompact_holomorphic_fin (n : ℕ) {S : Set (Fin n → ℂ)}
    (hS : IsCompact S) (hlocal : ∀ x ∈ S, AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S x) : S.Finite := by
  induction n with
  | zero => exact Set.toFinite S
  | succ n ih =>
    let e : ((Fin n → ℂ) × ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ) :=
      (ContinuousLinearEquiv.prodComm ℂ (Fin n → ℂ) ℂ).trans
        (Fin.consEquivL ℂ (fun _ : Fin (n + 1) => ℂ))
    let T := e ⁻¹' S
    have hT : IsCompact T := e.toHomeomorph.isClosedEmbedding.isCompact_preimage hS
    have hTlocal : ∀ p ∈ T, AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt T p := fun p hp =>
      (hlocal (e p) hp).preimage isOpen_univ (mem_univ p) e.differentiable.differentiableOn
    have hP : IsCompact (Prod.fst '' T) := hT.image continuous_fst
    have hPfinite : (Prod.fst '' T).Finite := ih hP
      (fun x _ => compact_projection_holomorphic hT hTlocal x)
    have hTfinite : T.Finite := by
      apply (hPfinite.biUnion (fun x _ =>
        (finite_vertical_fiber hT hTlocal x).image (fun z => (x, z)))).subset
      intro p hp
      exact mem_iUnion.mpr ⟨p.1, mem_iUnion.mpr
        ⟨⟨p, hp, rfl⟩, ⟨p.2, hp, rfl⟩⟩⟩
    exact hTfinite.of_preimage e.surjective

theorem finite_of_isCompact_holomorphic
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    {S : Set V} (hS : IsCompact S) (hlocal : ∀ x ∈ S, AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S x) : S.Finite := by
  let e : (Fin (Module.finrank ℂ V) → ℂ) ≃L[ℂ] V :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hcompact := e.toHomeomorph.isClosedEmbedding.isCompact_preimage hS
  have hfinite := finite_of_isCompact_holomorphic_fin (Module.finrank ℂ V) hcompact
    (fun x hx => (hlocal (e x) hx).preimage isOpen_univ (mem_univ x)
      e.differentiable.differentiableOn)
  exact hfinite.of_preimage e.surjective

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.CompactAnalyticAt.Constructions.CompactAnalytic
