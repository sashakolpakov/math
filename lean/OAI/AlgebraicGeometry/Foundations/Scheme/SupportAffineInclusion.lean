import OAI.AlgebraicGeometry.Foundations.Scheme.SupportAffineQuotient

/-! # Support Affine Inclusion -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.SupportAffineInclusion

noncomputable section

/-!
# Strict inclusion of irreducible supports on a common affine open

A nonempty open part of an irreducible closed set is dense in that closed set.
Consequently a proper closed subset cannot become the entire support after
restriction to an open meeting it. On an affine open, the actual vanishing
ideals of the two reduced supports are therefore strictly nested in the
opposite direction. The quotient rings are those of `SupportAffineQuotient`.

These statements require no finite-type or dimension hypothesis.
-/

open _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

section Topology

variable {T : Type u} [TopologicalSpace T]

/-- Every nonempty open part of an irreducible closed set has that entire
closed set as its ambient closure. -/
theorem irreducibleCloseds_closure_inter_open (W : IrreducibleCloseds T)
    (U : Opens T) (hWU : ((W : Set T) ∩ (U : Set T)).Nonempty) :
    closure ((W : Set T) ∩ (U : Set T)) = (W : Set T) := by
  apply Set.Subset.antisymm
  · exact closure_minimal Set.inter_subset_left W.isClosed
  · exact subset_closure_inter_of_isPreirreducible_of_isOpen
      W.isIrreducible.2 U.isOpen hWU

/-- Proper inclusion of irreducible closed supports persists on every open
set meeting the smaller support. -/
theorem irreducibleCloseds_inter_open_ssubset (Z W : IrreducibleCloseds T)
    (hZW : Z < W) (U : Opens T)
    (hZU : ((Z : Set T) ∩ (U : Set T)).Nonempty) :
    (Z : Set T) ∩ (U : Set T) ⊂ (W : Set T) ∩ (U : Set T) := by
  have hWU : ((W : Set T) ∩ (U : Set T)).Nonempty := by
    obtain ⟨x, hxZ, hxU⟩ := hZU
    exact ⟨x, hZW.le hxZ, hxU⟩
  rw [Set.ssubset_def]
  refine ⟨Set.inter_subset_inter_left _ hZW.le, ?_⟩
  intro h
  apply (not_le_of_gt hZW)
  have hsub : closure ((W : Set T) ∩ (U : Set T)) ⊆ (Z : Set T) :=
    closure_minimal (h.trans Set.inter_subset_left) Z.isClosed
  rwa [irreducibleCloseds_closure_inter_open W U hWU] at hsub

end Topology

variable {X : Scheme.{u}}

/-- The support's inverse-image open is nonempty precisely when the ambient
open meets the support. -/
theorem supportAffineOpen_nonempty_iff (Z : IrreducibleCloseds X)
    (U : X.affineOpens) :
    Nonempty (SupportAffineQuotient.supportAffineOpen Z U) ↔
      ((Z : Set X) ∩ (U.1 : Set X)).Nonempty := by
  constructor
  · rintro ⟨⟨x, hx⟩⟩
    refine ⟨CycleClass.Geometric.GenericPoint.reducedSupportι Z x, ?_, hx⟩
    rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι Z]
    exact ⟨x, rfl⟩
  · rintro ⟨x, hxZ, hxU⟩
    rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι Z] at hxZ
    obtain ⟨y, rfl⟩ := hxZ
    exact ⟨⟨y, hxU⟩⟩

/-- An affine open meeting the smaller support also meets every containing
support. -/
theorem supportAffineOpen_nonempty_of_le (Z W : IrreducibleCloseds X)
    (hZW : Z ≤ W) (U : X.affineOpens) [Nonempty (SupportAffineQuotient.supportAffineOpen Z U)] :
    Nonempty (SupportAffineQuotient.supportAffineOpen W U) := by
  apply (supportAffineOpen_nonempty_iff W U).mpr
  obtain ⟨x, hxZ, hxU⟩ := (supportAffineOpen_nonempty_iff Z U).mp inferInstance
  exact ⟨x, hZW hxZ, hxU⟩

/-- Every irreducible support meets an actual affine open of the ambient scheme. -/
theorem exists_supportAffineOpen_nonempty (Z : IrreducibleCloseds X) :
    ∃ U : X.affineOpens, Nonempty (SupportAffineQuotient.supportAffineOpen Z U) := by
  obtain ⟨x, hxZ⟩ := Z.isIrreducible.nonempty
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  exact ⟨⟨U, hU⟩, (supportAffineOpen_nonempty_iff Z ⟨U, hU⟩).mpr ⟨x, hxZ, hxU⟩⟩

/-- Nested irreducible supports admit a common ambient affine open meeting both. -/
theorem exists_common_supportAffineOpen (Z W : IrreducibleCloseds X)
    (hZW : Z ≤ W) :
    ∃ U : X.affineOpens,
      Nonempty (SupportAffineQuotient.supportAffineOpen Z U) ∧ Nonempty (SupportAffineQuotient.supportAffineOpen W U) := by
  obtain ⟨U, hU⟩ := exists_supportAffineOpen_nonempty Z
  let : Nonempty (SupportAffineQuotient.supportAffineOpen Z U) := hU
  exact ⟨U, hU, supportAffineOpen_nonempty_of_le Z W hZW U⟩

/-- An ambient affine open meeting a support contains its generic point. -/
theorem support_genericPoint_mem_affineOpen (Z : IrreducibleCloseds X)
    (U : X.affineOpens) [Nonempty (SupportAffineQuotient.supportAffineOpen Z U)] :
    irreducibleSetEquivPoints Z ∈ U.1 := by
  apply (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem_open_set_iff
    U.1.isOpen |>.mpr
  exact (supportAffineOpen_nonempty_iff Z U).mp inferInstance

/-- Inverse images in the actual affine spectrum preserve the strict support
inclusion whenever that affine open meets the smaller support. -/
theorem supportAffine_preimage_ssubset (Z W : IrreducibleCloseds X)
    (hZW : Z < W) (U : X.affineOpens) [Nonempty (SupportAffineQuotient.supportAffineOpen Z U)] :
    U.2.fromSpec ⁻¹' (Z : Set X) ⊂ U.2.fromSpec ⁻¹' (W : Set X) := by
  have h := irreducibleCloseds_inter_open_ssubset Z W hZW U.1
    ((supportAffineOpen_nonempty_iff Z U).mp inferInstance)
  rw [Set.ssubset_def] at h ⊢
  refine ⟨Set.preimage_mono hZW.le, ?_⟩
  intro hpre
  apply h.2
  intro x hx
  have hxRange : x ∈ Set.range U.2.fromSpec := by
    rw [U.2.range_fromSpec]
    exact hx.2
  obtain ⟨y, rfl⟩ := hxRange
  exact ⟨hpre hx.1, hx.2⟩

/-- Actual affine support ideals reverse inclusion. -/
theorem supportAffineIdeal_le (Z W : IrreducibleCloseds X)
    (hZW : Z ≤ W) (U : X.affineOpens) :
    (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W).ideal U ≤ (CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal U := by
  change PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (W : Set X)) ≤
    PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (Z : Set X))
  exact PrimeSpectrum.vanishingIdeal_anti_mono (Set.preimage_mono hZW)

/-- The vanishing ideals of proper nested supports are strictly nested in the
opposite direction on a common affine open meeting the smaller support. -/
theorem supportAffineIdeal_lt (Z W : IrreducibleCloseds X)
    (hZW : Z < W) (U : X.affineOpens) [Nonempty (SupportAffineQuotient.supportAffineOpen Z U)] :
    (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W).ideal U < (CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal U := by
  change PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (W : Set X)) <
    PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (Z : Set X))
  exact (PrimeSpectrum.vanishingIdeal_strict_anti_mono_iff
    (Z.isClosed.preimage U.2.fromSpec.continuous)
    (W.isClosed.preimage U.2.fromSpec.continuous)).mp
      (supportAffine_preimage_ssubset Z W hZW U)

end

end OAI.AlgebraicGeometry.Foundations.Scheme.SupportAffineInclusion
