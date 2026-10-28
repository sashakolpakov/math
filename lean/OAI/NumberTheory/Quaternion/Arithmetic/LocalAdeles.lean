import OAI.NumberTheory.ArithmeticGroups.Lattices.Algebraic

/-! # Local Adeles -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LocalAdeles

noncomputable section

/-! Concrete local and restricted adelic point spaces for Arithmetic.
This file does not assert strong approximation. -/

open scoped Classical _root_.NumberField RestrictedProduct
open Filter
open OAI.NumberTheory.ArithmeticGroups.Lattices.Algebraic

abbrev Place (F : Type) [Field F] :=
  NumberField.InfinitePlace F ⊕ IsDedekindDomain.HeightOneSpectrum (𝓞 F)

variable {F : Type} [Field F] [NumberField F]

def Completion : Place F → Type
  | .inl v => v.Completion
  | .inr v => v.adicCompletion F

instance completionField (v : Place F) : Field (LocalAdeles.Completion v) := by
  cases v with
  | inl v => exact inferInstanceAs (Field v.Completion)
  | inr v => exact inferInstanceAs (Field (v.adicCompletion F))

instance completionTopology (v : Place F) : TopologicalSpace (LocalAdeles.Completion v) := by
  cases v with
  | inl v => exact inferInstanceAs (TopologicalSpace v.Completion)
  | inr v => exact inferInstanceAs (TopologicalSpace (v.adicCompletion F))

instance completionTopologicalRing (v : Place F) : IsTopologicalRing (LocalAdeles.Completion v) := by
  cases v with
  | inl v => exact inferInstanceAs (IsTopologicalRing v.Completion)
  | inr v => exact inferInstanceAs (IsTopologicalRing (v.adicCompletion F))

def localEmbedding : (v : Place F) → F →+* LocalAdeles.Completion v
  | .inl v => algebraMap F v.Completion
  | .inr v => NumberField.FinitePlace.embedding v

def localIntegerRing : (v : Place F) → Subring (LocalAdeles.Completion v)
  | .inl _ => ⊤
  | .inr v => (v.adicCompletionIntegers F).toSubring

theorem localIntegerRing_isOpen (v : Place F) :
    IsOpen (localIntegerRing v : Set (LocalAdeles.Completion v)) := by
  cases v with
  | inl v => exact isOpen_univ
  | inr v => exact Valued.isOpen_valuationSubring (v.adicCompletion F)

variable {n : ℕ} (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)

abbrev LocalPoints (v : Place F) := G.Points (localEmbedding v)

def diagonalLocal (v : Place F) : G.RationalPoints →* LocalPoints G v :=
  G.map (RingHom.id F) (localEmbedding v)

@[simp] theorem diagonalLocal_entry (v : Place F) (g : G.RationalPoints)
    (i j : Fin n) :
    (diagonalLocal G v g).val i j = localEmbedding v (g.val i j) := rfl

/-- Integral invertible matrices in the fixed faithful representation.
Requiring integral inverse entries also makes sense independently of determinant one. -/
def integralLocalSubgroup (v : Place F) : Subgroup (LocalPoints G v) where
  carrier := {g | (∀ i j, g.val i j ∈ localIntegerRing v) ∧
    ∀ i j, (g⁻¹).val i j ∈ localIntegerRing v}
  one_mem' := by
    constructor <;> intro i j <;>
      simp only [inv_one, OneMemClass.coe_one, Matrix.SpecialLinearGroup.coe_one,
        Matrix.one_apply] <;> split_ifs <;> simp
  mul_mem' := by
    intro g h hg hh
    constructor
    · intro i j
      change ∑ k, g.val i k * h.val k j ∈ localIntegerRing v
      exact (localIntegerRing v).sum_mem fun k _ =>
        (localIntegerRing v).mul_mem (hg.1 i k) (hh.1 k j)
    · intro i j
      rw [mul_inv_rev]
      change ∑ k, (h⁻¹).val i k * (g⁻¹).val k j ∈ localIntegerRing v
      exact (localIntegerRing v).sum_mem fun k _ =>
        (localIntegerRing v).mul_mem (hh.2 i k) (hg.2 k j)
  inv_mem' := by
    intro g hg
    exact ⟨hg.2, by simpa only [inv_inv] using hg.1⟩

theorem local_entry_continuous (v : Place F) (i j : Fin n) :
    Continuous (fun g : LocalPoints G v => g.val i j) := by
  exact (continuous_apply j).comp
    (Matrix.SpecialLinearGroup.continuous_apply
      (fun g : LocalPoints G v => g.val) continuous_subtype_val i)

theorem integralLocalSubgroup_isOpen (v : Place F) :
    IsOpen (integralLocalSubgroup G v : Set (LocalPoints G v)) := by
  have he : IsOpen {g : LocalPoints G v | ∀ i j, g.val i j ∈ localIntegerRing v} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (localIntegerRing_isOpen v).preimage (local_entry_continuous G v i j)
  exact he.inter (he.preimage continuous_inv)

theorem eventually_integral_scalar (a : F) :
    ∀ᶠ v : Place F in cofinite, localEmbedding v a ∈ localIntegerRing v := by
  have hf := (algebraMap F (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) a).property
  rw [Filter.eventually_cofinite] at hf ⊢
  apply (hf.image (Sum.inr : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → Place F)).subset
  intro v hv
  cases v with
  | inl v => exact (hv (show localEmbedding (.inl v) a ∈ localIntegerRing (.inl v) from
      Subring.mem_top _)).elim
  | inr v => exact ⟨v, hv, rfl⟩

theorem eventually_integral_diagonal (g : G.RationalPoints) :
    ∀ᶠ v : Place F in cofinite, diagonalLocal G v g ∈ integralLocalSubgroup G v := by
  have hf : ∀ᶠ v : Place F in cofinite, ∀ i j : Fin n,
      localEmbedding v (g.val i j) ∈ localIntegerRing v :=
    Filter.eventually_all.mpr fun i =>
      Filter.eventually_all.mpr fun j => eventually_integral_scalar (g.val i j)
  have hi : ∀ᶠ v : Place F in cofinite, ∀ i j : Fin n,
      localEmbedding v ((g⁻¹).val i j) ∈ localIntegerRing v :=
    Filter.eventually_all.mpr fun i =>
      Filter.eventually_all.mpr fun j => eventually_integral_scalar ((g⁻¹).val i j)
  filter_upwards [hf, hi] with v hv hi
  exact ⟨hv, by simpa only [← map_inv, diagonalLocal_entry] using hi⟩

/-- The restricted product topology, not the subspace topology of the full product. -/
abbrev AwayAdelicPoints (S : Finset (Place F)) :=
  Πʳ v : {v : Place F // v ∉ S}, [LocalPoints G v.val, integralLocalSubgroup G v.val]

instance awayAdelicTopologicalGroup (S : Finset (Place F)) :
    IsTopologicalGroup (AwayAdelicPoints G S) := by
  let : Fact (∀ v : {v : Place F // v ∉ S},
      IsOpen (integralLocalSubgroup G v.val : Set (LocalPoints G v.val))) :=
    ⟨fun v => integralLocalSubgroup_isOpen G v.val⟩
  exact inferInstance

def diagonalAway (S : Finset (Place F)) : G.RationalPoints →* AwayAdelicPoints G S where
  toFun g := ⟨fun v => diagonalLocal G v.val g,
    Subtype.val_injective.tendsto_cofinite (eventually_integral_diagonal G g)⟩
  map_one' := by
    apply RestrictedProduct.ext
    intro v
    exact map_one (diagonalLocal G v.val)
  map_mul' g h := by
    apply RestrictedProduct.ext
    intro v
    exact map_mul (diagonalLocal G v.val) g h

@[simp] theorem diagonalAway_apply (S : Finset (Place F)) (g : G.RationalPoints)
    (v : {v : Place F // v ∉ S}) :
    diagonalAway G S g v = diagonalLocal G v.val g := rfl

theorem diagonalLocal_injective (v : Place F) :
    Function.Injective (diagonalLocal G v) :=
  G.map_injective (RingHom.id F) (localEmbedding v)

theorem diagonalAway_injective (S : Finset (Place F)) (v : Place F) (hv : v ∉ S) :
    Function.Injective (diagonalAway G S) := by
  intro g h hgh
  apply diagonalLocal_injective G v
  exact congrArg (fun a : AwayAdelicPoints G S => a ⟨v, hv⟩) hgh

/-- A single local component has a continuous projection from the adelic group. -/
theorem awayAdelic_eval_continuous (S : Finset (Place F))
    (v : {v : Place F // v ∉ S}) :
    Continuous (fun a : AwayAdelicPoints G S => a v) :=
  RestrictedProduct.continuous_eval v

/-- The stated local noncompactness hypothesis is equivalent to noncompactness
of the product over the omitted places. -/
theorem noncompact_place_iff_noncompact_product (S : Finset (Place F)) :
    (∃ v : Place F, v ∈ S ∧ ¬ CompactSpace (LocalPoints G v)) ↔
      ¬ CompactSpace ((v : (S : Set (Place F))) → LocalPoints G v.val) := by
  constructor
  · rintro ⟨v, hv, hn⟩ hc
    let : CompactSpace ((w : (S : Set (Place F))) → LocalPoints G w.val) := hc
    have hi : IsCompact (Set.range
        (fun a : (w : (S : Set (Place F))) → LocalPoints G w.val => a ⟨v, hv⟩)) :=
      isCompact_range (continuous_apply (⟨v, hv⟩ : (S : Set (Place F))))
    rw [(Function.surjective_eval
      (β := fun w : (S : Set (Place F)) => LocalPoints G w.val)
      (⟨v, hv⟩ : (S : Set (Place F)))).range_eq] at hi
    exact hn ⟨hi⟩
  · intro hn
    by_contra h
    push Not at h
    let : ∀ v : (S : Set (Place F)), CompactSpace (LocalPoints G v.val) :=
      fun v => h v.val v.property
    exact hn inferInstance

end

end OAI.NumberTheory.Quaternion.Arithmetic.LocalAdeles
