import Mathlib

/-! # Irreducible Group -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.IrreducibleGroup.Construction

noncomputable section

/-! Irreducible components in groups with separately continuous multiplication. -/

open scoped Classical Pointwise
open Set _root_.Topology _root_.TopologicalSpace

theorem irreducible_mul_of_separate_continuity
    {H : Type*} [Group H] [TopologicalSpace H] [SeparatelyContinuousMul H]
    {A B : Set H} (hA : IsIrreducible A) (hB : IsIrreducible B) :
    IsIrreducible (A * B) := by
  refine ⟨hA.nonempty.mul hB.nonempty, ?_⟩
  intro U V hU hV hAU hBV
  obtain ⟨y, hy, hyU⟩ := hAU
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_mul.mp hy
  obtain ⟨z, hz, hzV⟩ := hBV
  obtain ⟨c, hc, d, hd, rfl⟩ := mem_mul.mp hz
  obtain ⟨t, ht, hat, hct⟩ := hB.2 ((a * ·) ⁻¹' U) ((c * ·) ⁻¹' V)
    (hU.preimage (continuous_const_mul a)) (hV.preimage (continuous_const_mul c))
    ⟨b, hb, hyU⟩ ⟨d, hd, hzV⟩
  obtain ⟨s, hs, hstU, hstV⟩ := hA.2 ((· * t) ⁻¹' U) ((· * t) ⁻¹' V)
    (hU.preimage (continuous_mul_const t)) (hV.preimage (continuous_mul_const t))
    ⟨a, ha, hat⟩ ⟨c, hc, hct⟩
  exact ⟨s * t, mul_mem_mul hs ht, hstU, hstV⟩

theorem irreducible_subset_identityComponent
    {H : Type*} [Group H] [TopologicalSpace H] [SeparatelyContinuousMul H]
    {A : Set H} (hA : IsIrreducible A) (hA1 : 1 ∈ A) :
    A ⊆ irreducibleComponent (1 : H) := by
  let C := irreducibleComponent (1 : H)
  have hC : IsIrreducible C := isIrreducible_irreducibleComponent
  have hprod : C * A ⊆ C :=
    (irreducibleComponent_mem_irreducibleComponents (1 : H)).2
      (irreducible_mul_of_separate_continuity hC hA)
      (fun c hc => ⟨c, hc, 1, hA1, mul_one c⟩)
  intro a ha
  exact hprod ⟨1, mem_irreducibleComponent, a, ha, one_mul a⟩

def irreducibleIdentitySubgroup (H : Type*) [Group H] [TopologicalSpace H]
    [SeparatelyContinuousMul H] [ContinuousInv H] : Subgroup H where
  carrier := irreducibleComponent (1 : H)
  one_mem' := mem_irreducibleComponent
  mul_mem' ha hb := irreducible_subset_identityComponent
    (irreducible_mul_of_separate_continuity
      isIrreducible_irreducibleComponent isIrreducible_irreducibleComponent)
    ⟨1, mem_irreducibleComponent, 1, mem_irreducibleComponent, one_mul 1⟩ (mul_mem_mul ha hb)
  inv_mem' hx := irreducible_subset_identityComponent
    (isIrreducible_irreducibleComponent.image Inv.inv continuous_inv.continuousOn)
    ⟨1, mem_irreducibleComponent, inv_one⟩ ⟨_, hx, rfl⟩

theorem irreducible_meeting_identityComponent_subset
    {H : Type*} [Group H] [TopologicalSpace H]
    [SeparatelyContinuousMul H] [ContinuousInv H]
    {A : Set H} (hA : IsIrreducible A)
    (hAC : (A ∩ irreducibleComponent (1 : H)).Nonempty) :
    A ⊆ irreducibleComponent (1 : H) := by
  obtain ⟨x, hxA, hxC⟩ := hAC
  have htranslate : (x⁻¹ * ·) '' A ⊆ irreducibleComponent (1 : H) :=
    irreducible_subset_identityComponent
      (hA.image _ (continuous_const_mul x⁻¹).continuousOn)
      ⟨x, hxA, inv_mul_cancel x⟩
  intro a ha
  have hxa := htranslate ⟨a, ha, rfl⟩
  have hc : x * (x⁻¹ * a) ∈ irreducibleComponent (1 : H) :=
    (irreducibleIdentitySubgroup H).mul_mem hxC hxa
  simpa only [mul_inv_cancel_left] using hc

theorem irreducible_identityComponent_open
    {H : Type*} [Group H] [TopologicalSpace H]
    [SeparatelyContinuousMul H] [ContinuousInv H] [NoetherianSpace H] :
    IsOpen (irreducibleComponent (1 : H)) := by
  let C := irreducibleComponent (1 : H)
  let S := irreducibleComponents H \ {C}
  have hS : S.Finite := NoetherianSpace.finite_irreducibleComponents.sdiff
  have hcomp : Cᶜ = ⋃ A ∈ S, A := by
    ext x
    constructor
    · intro hx
      refine mem_iUnion.mpr ⟨irreducibleComponent x, mem_iUnion.mpr ⟨?_, mem_irreducibleComponent⟩⟩
      refine ⟨irreducibleComponent_mem_irreducibleComponents x, ?_⟩
      intro he
      exact hx ((mem_singleton_iff.mp he) ▸ mem_irreducibleComponent)
    · intro hx
      obtain ⟨A, hA⟩ := mem_iUnion.mp hx
      obtain ⟨hAS, hxA⟩ := mem_iUnion.mp hA
      intro hxC
      have hAC : A ⊆ C := irreducible_meeting_identityComponent_subset hAS.1.1 ⟨x, hxA, hxC⟩
      have hCA : C ⊆ A := hAS.1.2 isIrreducible_irreducibleComponent hAC
      exact hAS.2 (mem_singleton_iff.mpr (Subset.antisymm hAC hCA))
  apply isClosed_compl_iff.mp
  rw [hcomp]
  exact hS.isClosed_biUnion fun A hA => isClosed_of_mem_irreducibleComponents A hA.1

theorem irreducible_of_connected_noetherian_group
    (H : Type*) [Group H] [TopologicalSpace H]
    [SeparatelyContinuousMul H] [ContinuousInv H] [NoetherianSpace H] [ConnectedSpace H] :
    IrreducibleSpace H := by
  have hclopen : IsClopen (irreducibleComponent (1 : H)) :=
    ⟨isClosed_irreducibleComponent, irreducible_identityComponent_open⟩
  have heq := hclopen.eq_univ ⟨1, mem_irreducibleComponent⟩
  apply (irreducibleSpace_def H).mpr
  change IsIrreducible (Set.univ : Set H)
  rw [← heq]
  exact isIrreducible_irreducibleComponent

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.IrreducibleGroup.Construction
