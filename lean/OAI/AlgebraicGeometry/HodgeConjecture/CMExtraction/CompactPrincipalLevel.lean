import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Groups
import Mathlib.Topology.Maps.Proper.Basic

/-! # Compact Principal Level -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CompactPrincipalLevel.Approximation

noncomputable section

/-! A continuous linear action has open principal levels on a compact
open lattice whenever the corresponding multiple of that lattice is open. -/

open scoped Classical

theorem compact_forall_mem_open {X V W : Type*}
    [TopologicalSpace X] [TopologicalSpace V] [TopologicalSpace W]
    (f : X × V → W) (hf : Continuous f) (K : Set V) (hK : IsCompact K)
    (U : Set W) (hU : IsOpen U) :
    IsOpen {x | ∀ v ∈ K, f (x, v) ∈ U} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun p : X × K => f (p.1, p.2.val)) :=
    hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hs : IsClosed {p : X × K | f (p.1, p.2.val) ∉ U} := hU.isClosed_compl.preimage hc
  have hp := isClosedMap_fst_of_compactSpace _ hs
  have he : {x | ∀ v ∈ K, f (x, v) ∈ U} =
      (Prod.fst '' {p : X × K | f (p.1, p.2.val) ∉ U})ᶜ := by
    ext x
    constructor
    · intro hx
      rintro ⟨⟨y, v⟩, hy, he⟩
      exact hy (he ▸ hx v.val v.property)
    · intro hx v hv
      by_contra h
      exact hx ⟨(x, ⟨v, hv⟩), h, rfl⟩
  rw [he]
  exact hp.isOpen_compl

variable {R V G : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [TopologicalSpace V] [IsTopologicalAddGroup V]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : G →* (V ≃ₗ[R] V)) (hρ : Continuous (fun p : G × V => ρ p.1 p.2))
  (L : AddSubgroup V) (hL : IsOpen (L : Set V)) (hLc : IsCompact (L : Set V)) (N : ℕ)

include hρ hL hLc in
theorem principal_lattice_comap_open
    (hN : IsOpen {z : V | ∃ y ∈ L, z = N • y}) :
    IsOpen ((AbelianModuli.ReferenceFamily.Groups.principalLatticeSubgroup (R := R) L N).comap ρ : Set G) := by
  let A : Set G := {g | ∀ x ∈ L, ρ g x ∈ L}
  let B : Set G := {g | ∀ x ∈ L, ρ g x - x ∈ {z : V | ∃ y ∈ L, z = N • y}}
  have hA : IsOpen A := compact_forall_mem_open _ hρ _ hLc _ hL
  have hB : IsOpen B := compact_forall_mem_open _ (hρ.sub continuous_snd) _ hLc _ hN
  have hcancel (g : G) (x : V) : ρ (g⁻¹) (ρ g x) = x := by
    rw [map_inv]
    exact (ρ g).symm_apply_apply x
  have hcancel' (g : G) (x : V) : ρ g (ρ (g⁻¹) x) = x := by
    rw [map_inv]
    exact (ρ g).apply_symm_apply x
  have he : ((AbelianModuli.ReferenceFamily.Groups.principalLatticeSubgroup (R := R) L N).comap ρ : Set G) =
      (A ∩ (fun g : G => g⁻¹) ⁻¹' A) ∩ B := by
    ext g
    change ((∀ x, x ∈ L ↔ ρ g x ∈ L) ∧ (∀ x ∈ L, ∃ y ∈ L, ρ g x - x = N • y)) ↔
      ((g ∈ A ∧ g⁻¹ ∈ A) ∧ g ∈ B)
    constructor
    · rintro ⟨hpres, hcong⟩
      refine ⟨⟨fun x hx => (hpres x).mp hx, ?_⟩, hcong⟩
      intro x hx
      exact (hpres (ρ (g⁻¹) x)).mpr ((hcancel' g x).symm ▸ hx)
    · rintro ⟨⟨hpos, hneg⟩, hcong⟩
      refine ⟨fun x => ⟨hpos x, fun hx => ?_⟩, hcong⟩
      exact hcancel g x ▸ hneg (ρ g x) hx
  rw [he]
  exact (hA.inter (hA.preimage continuous_inv)).inter hB

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CompactPrincipalLevel.Approximation
