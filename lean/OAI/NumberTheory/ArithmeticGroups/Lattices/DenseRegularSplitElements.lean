import OAI.NumberTheory.ArithmeticGroups.Lattices.KillingSplit
import Mathlib.Topology.Baire.Lemmas

/-! # Dense Regular Split Elements -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Regular points for a finite family of real linear forms are dense. -/

open scoped Classical

theorem DenseRegularSplitElements.Construction.regular_linear_forms_dense
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Finite ι]
    (w : ι → E →ₗ[ℝ] ℝ) : Dense {x : E | ∀ i, w i x = 0 ↔ w i = 0} := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let J := {i : ι // w i ≠ 0}
  have ho (i : J) : IsOpen {x : E | w i.val x ≠ 0} :=
    (isClosed_eq (w i.val).continuous_of_finiteDimensional continuous_const).isOpen_compl
  have hd (i : J) : Dense {x : E | w i.val x ≠ 0} := by
    change Dense (((w i.val).ker : Set E)ᶜ)
    rw [← interior_eq_empty_iff_dense_compl]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have he := (w i.val).ker.eq_top_of_nonempty_interior' ⟨x, hx⟩
    exact i.property (LinearMap.ker_eq_top.mp he)
  have h := dense_iInter_of_isOpen ho hd
  apply h.mono
  intro x hx i
  constructor
  · intro hi
    by_contra hn
    exact (Set.mem_iInter.mp hx ⟨i, hn⟩) hi
  · intro hi
    rw [hi]
    rfl

theorem KillingSplit.Construction.KillingSplitWeightData.regular_elements_dense
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplit.Construction.KillingSplitWeightData B) :
    Dense {A : d.subspace | ∀ i, d.weight i A = 0 ↔ d.weight i = 0} := by
  let : NormedAddCommGroup d.subspace := inferInstance
  let : NormedSpace ℝ d.subspace := inferInstance
  exact DenseRegularSplitElements.Construction.regular_linear_forms_dense (E := d.subspace) d.weight

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
