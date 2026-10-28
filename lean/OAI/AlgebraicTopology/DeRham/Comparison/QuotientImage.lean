import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Quotient Image -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.QuotientImage

/-!
# Images of a submodule after quotienting its source

These are elementary quotient-module facts used by a possible comparison
between closed pure forms and de Rham classes. All modules and maps below are
mathlib modules and the canonical mathlib quotient maps. No cohomology or Hodge
structure is postulated here.

If `P` is a submodule of `V`, `E` is the submodule killed in the target, and `B`
is a submodule of `P` whose elements lie in `E`, the canonical map
`P / B → V / E` has the same image for every such `B`. Its injectivity is the
strictly stronger assertion that `B` contains every element of `P` lying in `E`.

To apply this to the Clay definition of a Hodge component, actual spaces of
closed forms, exact forms, closed pure forms, and `d' d''` images must still be
constructed, and the containment for the last of these must be proved.
-/

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
variable (P E : Submodule R V) (B : Submodule R P)
variable (hB : B ≤ E.comap P.subtype)

/-- Quotienting the numerator by any submodule already killed in the target
does not change its image. -/
theorem range_submodule_quotient_map :
    LinearMap.range (B.mapQ E P.subtype hB) = P.map E.mkQ := by
  simpa only [Submodule.range_subtype] using
    (Submodule.range_mapQ B E P.subtype hB)

/-- A class is in the image precisely when it has a representative in `P`. -/
theorem mem_range_submodule_quotient_map_iff (y : V ⧸ E) :
    y ∈ LinearMap.range (B.mapQ E P.subtype hB) ↔
      ∃ x : V, x ∈ P ∧ E.mkQ x = y := by
  rw [range_submodule_quotient_map]
  exact Submodule.mem_map

/-- The preimage in the ambient module is `P + E`, independently of `B`. -/
theorem comap_range_submodule_quotient_map :
    (LinearMap.range (B.mapQ E P.subtype hB)).comap E.mkQ = P ⊔ E := by
  rw [range_submodule_quotient_map, Submodule.comap_map_mkQ, sup_comm]

/-- Membership of the class of an ambient element is membership in `P + E`. -/
theorem mkQ_mem_range_submodule_quotient_map_iff (x : V) :
    E.mkQ x ∈ LinearMap.range (B.mapQ E P.subtype hB) ↔ x ∈ P ⊔ E := by
  change x ∈ (LinearMap.range (B.mapQ E P.subtype hB)).comap E.mkQ ↔ _
  rw [comap_range_submodule_quotient_map]

/-- The kernel consists of classes of elements of `P` that already lie in `E`. -/
theorem ker_submodule_quotient_map :
    LinearMap.ker (B.mapQ E P.subtype hB) =
      (E.comap P.subtype).map B.mkQ := by
  exact Submodule.ker_mapQ B E P.subtype hB

/-- Injectivity requires equality with the full kernel, not merely containment.
In a forms application this is where an additional `d' d''` lemma is needed. -/
theorem injective_submodule_quotient_map_iff :
    Function.Injective (B.mapQ E P.subtype hB) ↔ B = E.comap P.subtype := by
  rw [← LinearMap.ker_eq_bot, ker_submodule_quotient_map, eq_bot_iff,
    Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ]
  exact ⟨fun h => le_antisymm hB h, fun h => h.ge⟩

/-- Surjectivity says that every ambient element is a sum from `P` and `E`. -/
theorem surjective_submodule_quotient_map_iff :
    Function.Surjective (B.mapQ E P.subtype hB) ↔ P ⊔ E = ⊤ := by
  rw [← LinearMap.range_eq_top, range_submodule_quotient_map,
    Submodule.map_mkQ_eq_top, sup_comm]

/-- Separate the exact kernel condition from the condition of spanning the target. -/
theorem bijective_submodule_quotient_map_iff :
    Function.Bijective (B.mapQ E P.subtype hB) ↔
      B = E.comap P.subtype ∧ P ⊔ E = ⊤ := by
  rw [Function.Bijective, injective_submodule_quotient_map_iff,
    surjective_submodule_quotient_map_iff]

end OAI.AlgebraicTopology.DeRham.Comparison.QuotientImage
