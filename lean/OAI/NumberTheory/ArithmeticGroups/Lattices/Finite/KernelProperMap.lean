import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Baire.LocallyCompactRegular

/-! # Kernel Proper Map -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.KernelProperMap.Construction

noncomputable section

/-! A continuous homomorphism from a sigma-compact group with finite
kernel and closed image in a locally compact group is proper. -/

open scoped Classical Pointwise
open Set

theorem hom_preimage_image_eq_mul_kernel
    {G H : Type*} [Group G] [Group H] (f : G →* H) (S : Set G) :
    f ⁻¹' (f '' S) = S * (f.ker : Set G) := by
  ext g
  constructor
  · rintro ⟨s, hs, hsg⟩
    refine ⟨s, hs, s⁻¹ * g, ?_, by simp⟩
    change f (s⁻¹ * g) = 1
    rw [map_mul, map_inv, ← hsg, inv_mul_cancel]
  · rintro ⟨s, hs, t, ht, rfl⟩
    refine ⟨s, hs, ?_⟩
    rw [map_mul, (show f t = 1 from ht), mul_one]

theorem surjective_open_hom_finite_kernel_proper
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H]
    (f : G →* H) [Finite f.ker] (hf : Continuous f) (hsurj : Function.Surjective f)
    (hopen : IsOpenMap f) : IsProperMap f := by
  have hquot := hopen.isQuotientMap hf hsurj
  have hclosed : IsClosedMap f := by
    intro S hS
    apply hquot.isClosed_preimage.mp
    rw [hom_preimage_image_eq_mul_kernel]
    exact hS.mul_right_of_isCompact (Set.toFinite (f.ker : Set G)).isCompact
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨hf, hclosed, fun y => ?_⟩
  obtain ⟨x, hx⟩ := hsurj y
  let j : (f ⁻¹' {y}) → f.ker := fun z => ⟨x⁻¹ * z.val, by
    change f (x⁻¹ * z.val) = 1
    rw [map_mul, map_inv, hx, (show f z.val = y from z.property), inv_mul_cancel]⟩
  let : Finite (f ⁻¹' {y}) := Finite.of_injective j (by
    intro z w h
    apply Subtype.ext
    exact mul_left_cancel (congrArg Subtype.val h))
  exact (Set.toFinite (f ⁻¹' {y})).isCompact

theorem continuous_hom_finite_kernel_closed_range_proper
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SigmaCompactSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]
    (f : G →* H) [Finite f.ker] (hf : Continuous f) (hclosed : IsClosed (Set.range f)) :
    IsProperMap f := by
  let : LocallyCompactSpace f.range := hclosed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let r : G →* f.range := f.rangeRestrict
  have hr : Continuous r := hf.subtype_mk _
  have hsurj : Function.Surjective r := by
    rintro ⟨y, x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  let j : r.ker → f.ker := fun x => ⟨x.val, congrArg Subtype.val x.property⟩
  let : Finite r.ker := Finite.of_injective j (by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : f.ker => z.val) h)
  have hproper : IsProperMap r := surjective_open_hom_finite_kernel_proper r hr hsurj
    (r.isOpenMap_of_sigmaCompact hsurj hr)
  exact hclosed.isClosedEmbedding_subtypeVal.isProperMap.comp hproper

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.KernelProperMap.Construction
