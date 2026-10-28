import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.Units

/-! # Compact Open Hecke -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CompactOpenHecke.Construction

noncomputable section

/-!
Compact open level subgroups have finite right-coset orbits, so their
raw double-coset Hecke operators are constructed without a finite-support
assumption. An open-embedding lemma for units supports the actual q-adic level.
-/

open _root_.Topology

section Units

variable {R S : Type*} [Monoid R] [Monoid S]

theorem units_map_range_of_injective (f : R →* S) (hf : Function.Injective f) :
    Set.range (Units.map f) = {u : Sˣ | (u : S) ∈ Set.range f ∧ ((u⁻¹ : Sˣ) : S) ∈ Set.range f} := by
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨⟨v.val, rfl⟩, ⟨v.inv, rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have hab : a * b = 1 := hf (by rw [map_mul, ha, hb, map_one]; exact u.mul_inv)
    have hba : b * a = 1 := hf (by rw [map_mul, hb, ha, map_one]; exact u.inv_mul)
    exact ⟨⟨a, b, hab, hba⟩, Units.ext ha⟩

variable [TopologicalSpace R] [TopologicalSpace S]

/-- An open monoid embedding induces an open embedding of unit groups,
with their standard topology recording both value and inverse. -/
theorem units_map_openEmbedding (f : R →* S) (hf : IsOpenEmbedding f) :
    IsOpenEmbedding (Units.map f) := by
  have he : IsEmbedding (Units.map f) := by
    open MulOpposite in
    have hprod := hf.isEmbedding.prodMap
      (opHomeomorph.isEmbedding.comp (hf.isEmbedding.comp opHomeomorph.symm.isEmbedding))
    have hcomp := hprod.comp Units.isEmbedding_embedProduct
    exact Units.isEmbedding_embedProduct.of_comp_iff.mp hcomp
  refine ⟨he, ?_⟩
  rw [units_map_range_of_injective f hf.injective]
  exact (hf.isOpen_range.preimage Units.continuous_val).inter
    (hf.isOpen_range.preimage Units.continuous_coe_inv)

end Units

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : Subgroup G)

/-- The image of a compact level orbit in the discrete coset space is
finite. This proves finite support for every double coset. -/
theorem rawRightCosetSupport_finite_of_compact_open
    (hopen : IsOpen (U : Set G)) (hcompact : IsCompact (U : Set G)) (g : G) :
    (Hecke.Construction.rawRightCosetSupport U g).Finite := by
  have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hopen
  have hset : (fun k : G => QuotientGroup.mk (k * g⁻¹)) '' (U : Set G) =
      Hecke.Construction.rawRightCosetSupport U g := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact MulAction.mem_orbit _ (⟨k, hk⟩ : U)
    · intro hx
      obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp hx
      exact ⟨k, k.property, hk⟩
  have h : IsCompact ((fun k : G => (QuotientGroup.mk (k * g⁻¹) : G ⧸ U)) '' (U : Set G)) :=
    hcompact.image (QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const))
  rw [hset] at h
  exact h.finite_of_discrete

/-- Every double coset at a compact open level has its unique raw
spherical Hecke operator, with no supplied operator or support witness. -/
theorem compact_open_raw_hecke_exists_unique
    (hopen : IsOpen (U : Set G)) (hcompact : IsCompact (U : Set G)) (g : G) :
    ∃! T : TateComparison.HeckeKernel.SphericalHecke U, TateComparison.HeckeKernel.IsRawDoubleCoset U g T := by
  let hfinite := rawRightCosetSupport_finite_of_compact_open U hopen hcompact g
  refine ⟨Hecke.Construction.rawDoubleCosetOperator U g hfinite, Hecke.Construction.rawDoubleCosetOperator_spec U g hfinite, ?_⟩
  intro T hT
  exact TateComparison.HeckeKernel.rawDoubleCoset_unique U hT (Hecke.Construction.rawDoubleCosetOperator_spec U g hfinite)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CompactOpenHecke.Construction
