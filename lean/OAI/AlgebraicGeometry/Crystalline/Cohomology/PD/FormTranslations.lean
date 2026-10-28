import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormSlots

/-! # Form Translations -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormTranslations.PDFormTranslations

noncomputable section

/-! # Relative differential symbols are unchanged by ambient constants -/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (δ : DividedPowers I)

theorem update_add_base {n : ℕ} (a : A) (v : Fin n → A) (i : Fin n) (r : R) :
    DeRham.PDDeRham.symbol R A I δ a (Function.update v i (algebraMap R A r + v i)) =
      DeRham.PDDeRham.symbol R A I δ a v := by
  have h := map_add (FormSlots.PDFormSlots.derivation R A I δ v i) (algebraMap R A r) (v i)
  rw [Derivation.map_algebraMap, zero_add] at h
  change DeRham.PDDeRham.symbol R A I δ 1 (Function.update v i (algebraMap R A r + v i)) =
    DeRham.PDDeRham.symbol R A I δ 1 (Function.update v i (v i)) at h
  rw [Function.update_eq_self] at h
  exact (DeRham.PDDeRham.symbol_smul_one R A I δ a _).trans
    ((congrArg (a • ·) h).trans (DeRham.PDDeRham.symbol_smul_one R A I δ a v).symm)

theorem add_base {n : ℕ} (a : A) (v : Fin n → A) (r : Fin n → R) :
    DeRham.PDDeRham.symbol R A I δ a (fun i => algebraMap R A (r i) + v i) =
      DeRham.PDDeRham.symbol R A I δ a v := by
  classical
  let w : Finset (Fin n) → Fin n → A := fun s i => if i ∈ s then algebraMap R A (r i) + v i else v i
  have hs : ∀ s, DeRham.PDDeRham.symbol R A I δ a (w s) = DeRham.PDDeRham.symbol R A I δ a v := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have hw : w ∅ = v := by funext i; simp only [w, Finset.notMem_empty, ite_false]
      rw [hw]
    | @insert i s hi ih =>
      have hw : w (insert i s) = Function.update (w s) i (algebraMap R A (r i) + w s i) := by
        funext j
        by_cases hj : j = i
        · subst j
          simp only [w, Finset.mem_insert_self, ite_true, Function.update_self, hi, ite_false]
        · simp only [w, Finset.mem_insert, hj, false_or, Function.update_of_ne hj]
      rw [hw, update_add_base]
      exact ih
  have hw : w Finset.univ = fun i => algebraMap R A (r i) + v i := by
    funext i
    simp only [w, Finset.mem_univ, ite_true]
  exact hw ▸ hs Finset.univ

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormTranslations.PDFormTranslations
