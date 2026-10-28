import OAI.ArithmeticGeometry.Models.SpreadingOut.SplitCoproducts

/-! # Open Partition Iso -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.OpenPartitionIso.Construction

noncomputable section

/-! A covering disjoint open partition gives an isomorphism from its
scheme coproduct to the original scheme, respecting the structural map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem over_open_partition_sum_isIso
    {S : Scheme.{u}} {ι : Type u} (X : Over S) (C : ι → X.left.Opens)
    (hdis : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hcover : (⨆ i, C i) = ⊤) :
    IsIso (ProperCoproducts.Construction.overSigmaDesc (fun i ↦ OpenOver.Construction.overOpenInclusion X (C i))).left := by
  let q := (ProperCoproducts.Construction.overSigmaDesc (fun i ↦ OpenOver.Construction.overOpenInclusion X (C i))).left
  have : IsOpenImmersion q := by
    apply isOpenImmersion_sigmaDesc (fun i ↦ (C i).toScheme) (fun i ↦ (C i).ι)
    intro i j hij
    simpa only [Scheme.Opens.range_ι] using (Opens.coe_disjoint).mpr (hdis i j hij)
  have : Surjective q := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⨆ i, C i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨i, ⟨x, hi⟩, rfl⟩
  exact (isIso_iff_isOpenImmersion_and_surjective q).mpr ⟨inferInstance, inferInstance⟩

def overOpenPartitionIso
    {S : Scheme.{u}} {ι : Type u} (X : Over S) (C : ι → X.left.Opens)
    (hdis : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hcover : (⨆ i, C i) = ⊤) : ProperCoproducts.Construction.overSigma (fun i ↦ OpenOver.Construction.overOpen X (C i)) ≅ X := by
  let q := ProperCoproducts.Construction.overSigmaDesc (fun i ↦ OpenOver.Construction.overOpenInclusion X (C i))
  have : IsIso q.left := over_open_partition_sum_isIso X C hdis hcover
  exact Over.isoMk (asIso q.left) q.w

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.OpenPartitionIso.Construction
