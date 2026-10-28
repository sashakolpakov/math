import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.RingHom.Flat

/-! # Flat Ring Union -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.FlatRingUnion

noncomputable section

/-! # Flat ring maps from simultaneous finite lifts into flat ring maps -/

variable {B C : Type*} [CommRing B] [CommRing C] (f : B →+* C)
  {ι : Type*} (B' C' : ι → Type*) [∀ i, CommRing (B' i)] [∀ i, CommRing (C' i)]
  (a : ∀ i, B' i →+* B) (b : ∀ i, C' i →+* C) (g : ∀ i, B' i →+* C' i)

theorem flat (hg : ∀ i, (g i).Flat)
    (hcomm : ∀ i r, b i (g i r) = f (a i r))
    (hb : ∀ i, Function.Injective (b i))
    (hlift : ∀ {n : ℕ} (r : Fin n → B) (x : Fin n → C),
      ∃ i, ∃ r' : Fin n → B' i, ∃ x' : Fin n → C' i,
        (∀ j, a i (r' j) = r j) ∧ (∀ j, b i (x' j) = x j)) : f.Flat := by
  classical
  let := f.toAlgebra
  change Module.Flat B C
  apply Module.Flat.of_forall_isTrivialRelation
  intro n r x hrx
  change ∑ j, f (r j) * x j = 0 at hrx
  obtain ⟨i, r', x', hr, hx⟩ := hlift r x
  let := (g i).toAlgebra
  have : Module.Flat (B' i) (C' i) := hg i
  have hrel : ∑ j, r' j • x' j = 0 := by
    apply hb i
    change b i (∑ j, g i (r' j) * x' j) = b i 0
    simpa only [map_sum, map_mul, hcomm, hr, hx, map_zero] using hrx
  obtain ⟨k, d, y, hy, hd⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  refine ⟨k, fun j l => a i (d j l), fun l => b i (y l), ?_, ?_⟩
  · intro j
    change x j = ∑ l, f (a i (d j l)) * b i (y l)
    have he := congrArg (b i) (hy j)
    change b i (x' j) = b i (∑ l, g i (d j l) * y l) at he
    simpa only [hx, map_sum, map_mul, hcomm] using he
  · intro l
    have he := congrArg (a i) (hd l)
    simpa only [map_sum, map_mul, hr, map_zero] using he

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.FlatRingUnion
