import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Computable coordinate splitting for an explicit packing

The inverse uses a finite sum of equality-tested coordinate copies, followed
by a residual-coordinate lookup. None of the definitions chooses a basis or
uses classical choice. Finite types, embeddings, and coordinate values are
inputs; this is not a Turing-machine cost theorem.
-/

namespace SubexponentialSAT.ComputablePackingSplit

open scoped BigOperators

section Scatter

variable {K U V : Type*} [Semiring K] [Fintype U] [DecidableEq V]

/-- Finite scatter along an explicit injection. -/
def scatter (e : U ↪ V) : (U → K) →ₗ[K] (V → K) where
  toFun x v := ∑ u, if e u = v then x u else 0
  map_add' x y := by
    funext v
    change (∑ u, if e u = v then x u + y u else 0) =
      (∑ u, if e u = v then x u else 0) + ∑ u, if e u = v then y u else 0
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> simp
  map_smul' c x := by
    funext v
    change (∑ u, if e u = v then c * x u else 0) =
      c * ∑ u, if e u = v then x u else 0
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> simp

@[simp] theorem scatter_apply (e : U ↪ V) (x : U → K) (v : V) :
    scatter e x v = ∑ u, if e u = v then x u else 0 := rfl

@[simp] theorem scatter_on_image (e : U ↪ V) (x : U → K) (u : U) :
    scatter e x (e u) = x u := by
  classical
  simp only [scatter_apply, e.injective.eq_iff, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

theorem scatter_outside (e : U ↪ V) (x : U → K) (v : V)
    (hv : v ∉ Set.range e) : scatter e x v = 0 := by
  rw [scatter_apply]
  apply Finset.sum_eq_zero
  intro u _
  have hu : e u ≠ v := fun h => hv ⟨u, h⟩
  simp only [hu, ite_false]

/-- The coordinates absent from the supplied packing. -/
abbrev Leftover (e : U ↪ V) := {v : V // v ∉ Set.range e}

/-- Copy a residual coordinate when it is absent from the embedding, and
return zero on every packed coordinate. Range membership is a finite search. -/
def leftoverExtend (e : U ↪ V) : (Leftover e → K) →ₗ[K] (V → K) where
  toFun x v := if hv : v ∈ Set.range e then 0 else x ⟨v, hv⟩
  map_add' x y := by
    funext v
    by_cases hv : ∃ u, e u = v <;> simp [Set.mem_range, hv]
  map_smul' c x := by
    funext v
    by_cases hv : ∃ u, e u = v <;> simp [Set.mem_range, hv]

@[simp] theorem leftoverExtend_on_image (e : U ↪ V) (x : Leftover e → K) (u : U) :
    leftoverExtend e x (e u) = 0 := by
  simp [leftoverExtend ]

@[simp] theorem leftoverExtend_outside (e : U ↪ V) (x : Leftover e → K)
    (v : V) (hv : v ∉ Set.range e) : leftoverExtend e x v = x ⟨v, hv⟩ := by
  simp only [Set.mem_range] at hv
  simp [leftoverExtend, hv]

end Scatter

section Packing

variable {K I U V : Type*} [Semiring K] [Fintype I] [Fintype U] [DecidableEq V]

/-- Computable conversion between curried block coordinates and pair coordinates. -/
def uncurryLinear : (I → U → K) →ₗ[K] (I × U → K) where
  toFun x z := x z.1 z.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Assemble the packed blocks and the residual coordinates by finite copying. -/
def assemble (e : I × U ↪ V) :
    ((I → U → K) × (Leftover e → K)) →ₗ[K] (V → K) :=
  (scatter e).comp (uncurryLinear.comp
    (LinearMap.fst K (I → U → K) (Leftover e → K))) +
  (leftoverExtend e).comp (LinearMap.snd K (I → U → K) (Leftover e → K))

theorem assemble_eq (e : I × U ↪ V)
    (x : (I → U → K) × (Leftover e → K)) :
    assemble e x = scatter e (fun z => x.1 z.1 z.2) + leftoverExtend e x.2 := rfl

@[simp] theorem assemble_on_block (e : I × U ↪ V)
    (x : (I → U → K) × (Leftover e → K)) (i : I) (u : U) :
    assemble e x (e (i, u)) = x.1 i u := by
  rw [assemble_eq]
  simp only [Pi.add_apply, scatter_on_image, leftoverExtend_on_image, add_zero]

@[simp] theorem assemble_outside (e : I × U ↪ V)
    (x : (I → U → K) × (Leftover e → K)) (v : V) (hv : v ∉ Set.range e) :
    assemble e x v = x.2 ⟨v, hv⟩ := by
  rw [assemble_eq]
  simp only [Pi.add_apply, scatter_outside e _ v hv,
    leftoverExtend_outside e _ v hv, zero_add]

/-- An executable coordinate split for a supplied block embedding.
The forward map restricts; the inverse uses `assemble`, with no chosen basis. -/
def split (e : I × U ↪ V) :
    (V → K) ≃ₗ[K] ((I → U → K) × (Leftover e → K)) where
  toFun x := (fun i u => x (e (i, u)), fun v => x v.val)
  invFun := assemble e
  left_inv x := by
    funext v
    by_cases hv : v ∈ Set.range e
    · obtain ⟨⟨i, u⟩, rfl⟩ := hv
      exact assemble_on_block e _ i u
    · exact assemble_outside e _ v hv
  right_inv x := by
    apply Prod.ext
    · funext i u
      exact assemble_on_block e x i u
    · funext v
      exact assemble_outside e x v.val v.property
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem split_apply_block (e : I × U ↪ V) (x : V → K) (i : I) (u : U) :
    (split e x).1 i u = x (e (i, u)) := rfl

@[simp] theorem split_apply_leftover (e : I × U ↪ V) (x : V → K) (v : Leftover e) :
    (split e x).2 v = x v.val := rfl

@[simp] theorem split_symm_apply (e : I × U ↪ V)
    (x : (I → U → K) × (Leftover e → K)) :
    (split e).symm x = assemble e x := rfl

/-- The executable inverse formula, down to the finite equality-tested sum. -/
theorem split_symm_apply_eq_sum (e : I × U ↪ V)
    (x : (I → U → K) × (Leftover e → K)) (v : V) :
    (split e).symm x v =
      (∑ z : I × U, if e z = v then x.1 z.1 z.2 else 0) +
        (if hv : v ∈ Set.range e then 0 else x.2 ⟨v, hv⟩) := rfl

end Packing

section Cardinalities

variable {I U V : Type*} [Fintype I] [Fintype U] [Fintype V] [DecidableEq V]

theorem card_leftover (e : I × U ↪ V) :
    Fintype.card (Leftover e) = Fintype.card V - Fintype.card I * Fintype.card U := by
  rw [Fintype.card_subtype_compl, Fintype.card_range e, Fintype.card_prod]

omit [DecidableEq V] in
theorem card_blocks_le (e : I × U ↪ V) :
    Fintype.card I * Fintype.card U ≤ Fintype.card V := by
  simpa only [Fintype.card_prod] using Fintype.card_le_of_injective e e.injective

theorem card_blocks_add_leftover (e : I × U ↪ V) :
    Fintype.card I * Fintype.card U + Fintype.card (Leftover e) = Fintype.card V := by
  rw [card_leftover]
  exact Nat.add_sub_of_le (card_blocks_le e)

end Cardinalities

end SubexponentialSAT.ComputablePackingSplit

end OAI.Algorithms
