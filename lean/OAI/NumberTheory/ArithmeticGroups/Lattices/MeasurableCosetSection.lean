import OAI.NumberTheory.ArithmeticGroups.Lattices.FiniteDomainMeasureRigidity
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Measurable Coset Section -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.MeasurableCosetSection.Construction

noncomputable section

/-! Discrete coset quotients admit measurable representatives, selected
from a countable family of local quotient slices. -/

open scoped Classical
open Set _root_.MeasureTheory

theorem exists_measurable_coset_transversal
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (Γ : Subgroup H) [DiscreteTopology Γ] [Countable Γ] :
    ∃ D : Set H, MeasurableSet D ∧
      Function.Bijective (fun x : D => (QuotientGroup.mk x.val : H ⧸ Γ)) := by
  have hcover : IsQuotientCoveringMap (QuotientGroup.mk : H → H ⧸ Γ) Γ.op :=
    isQuotientMap_quotient_mk'.isQuotientCoveringMap_of_subgroupOp Γ
      (isDiscrete_iff_discreteTopology.mpr inferInstance) QuotientGroup.eq
  obtain ⟨U, hU, hinj, hUc⟩ := FiniteDomainMeasureRigidity.Construction.exists_countable_slices_of_quotientCovering hcover
  let D := ⋃ n, FiniteDomainMeasureRigidity.Construction.firstOrbitSlice (G := Γ.op) U n
  have hD : MeasurableSet D :=
    MeasurableSet.iUnion (FiniteDomainMeasureRigidity.Construction.firstOrbitSlice_measurable U (fun n => (hU n).measurableSet))
  have huniq : ∀ x (g h : Γ.op), g • x ∈ D → h • x ∈ D → g = h := by
    intro x g h hg hh
    obtain ⟨i, hi⟩ := mem_iUnion.mp hg
    obtain ⟨j, hj⟩ := mem_iUnion.mp hh
    exact FiniteDomainMeasureRigidity.Construction.firstOrbitSlice_unique U hinj x hi hj
  refine ⟨D, hD, ?_, ?_⟩
  · intro x y hxy
    have hm : x.val⁻¹ * y.val ∈ Γ := QuotientGroup.eq.mp hxy
    let g : Γ.op := ⟨MulOpposite.op (x.val⁻¹ * y.val), hm⟩
    have hg : g • x.val = y.val := by
      change x.val * (x.val⁻¹ * y.val) = y.val
      exact mul_inv_cancel_left _ _
    have hgone : g = 1 := huniq x.val g 1 (hg.symm ▸ y.property)
      (by simpa only [one_smul] using x.property)
    apply Subtype.ext
    simpa only [hgone, one_smul] using hg
  · intro q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    obtain ⟨n, g, hg⟩ := FiniteDomainMeasureRigidity.Construction.exists_firstOrbitSlice (G := Γ.op) U x (by
      obtain ⟨n, hn⟩ := hUc x
      exact ⟨n, 1, by simpa only [one_smul] using hn⟩)
    refine ⟨⟨g • x, mem_iUnion.mpr ⟨n, hg⟩⟩, ?_⟩
    exact QuotientGroup.mk_mul_of_mem x g.property

theorem exists_measurable_coset_section
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [PolishSpace H] [MeasurableSpace H] [BorelSpace H]
    (Γ : Subgroup H) [DiscreteTopology Γ] [Countable Γ]
    [MeasurableSpace (H ⧸ Γ)] [BorelSpace (H ⧸ Γ)] [T2Space (H ⧸ Γ)] :
    ∃ σ : H ⧸ Γ → H, Measurable σ ∧ Function.RightInverse σ QuotientGroup.mk := by
  obtain ⟨D, hD, hbij⟩ := exists_measurable_coset_transversal Γ
  let p : D → H ⧸ Γ := fun x => QuotientGroup.mk x.val
  let : StandardBorelSpace D := hD.standardBorel
  let : Nonempty D := ⟨(hbij.2 (QuotientGroup.mk (1 : H))).choose⟩
  have hp : Measurable p := QuotientGroup.continuous_mk.measurable.comp measurable_subtype_coe
  have he : MeasurableEmbedding p := hp.measurableEmbedding hbij.1
  refine ⟨fun q => (he.invFun q).val, measurable_subtype_coe.comp he.measurable_invFun, ?_⟩
  exact he.leftInverse_invFun.rightInverse_of_surjective hbij.2

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.MeasurableCosetSection.Construction
