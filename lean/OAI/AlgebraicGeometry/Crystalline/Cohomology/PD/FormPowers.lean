import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormSlots

/-! # Form Powers -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormPowers.PDFormPowers

noncomputable section

/-! # Power-coordinate Jacobians on actual divided-power differential symbols -/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (δ : DividedPowers I)

theorem update_pow {n : ℕ} (a : A) (v : Fin n → A) (i : Fin n) (m : ℕ) :
    DeRham.PDDeRham.symbol R A I δ a (Function.update v i (v i ^ m)) =
      DeRham.PDDeRham.symbol R A I δ (a * ((m : A) * v i ^ (m - 1))) v := by
  have h := (FormSlots.PDFormSlots.derivation R A I δ v i).leibniz_pow (v i) m
  rw [← Nat.cast_smul_eq_nsmul A, smul_smul] at h
  change DeRham.PDDeRham.symbol R A I δ 1 (Function.update v i (v i ^ m)) =
    ((m : A) * v i ^ (m - 1)) • DeRham.PDDeRham.symbol R A I δ 1 (Function.update v i (v i)) at h
  rw [Function.update_eq_self] at h
  rw [DeRham.PDDeRham.symbol_smul_one, h, smul_smul, ← DeRham.PDDeRham.symbol_smul_one]

theorem pow {n : ℕ} (a : A) (v : Fin n → A) (m : ℕ) :
    DeRham.PDDeRham.symbol R A I δ a (fun i => v i ^ m) =
      DeRham.PDDeRham.symbol R A I δ (a * ∏ i, ((m : A) * v i ^ (m - 1))) v := by
  classical
  let w : Finset (Fin n) → Fin n → A := fun s i => if i ∈ s then v i ^ m else v i
  have hs : ∀ s (b : A), DeRham.PDDeRham.symbol R A I δ b (w s) =
      DeRham.PDDeRham.symbol R A I δ (b * ∏ i ∈ s, ((m : A) * v i ^ (m - 1))) v := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro b
      have hw : w ∅ = v := by funext i; simp only [w, Finset.notMem_empty, ite_false]
      rw [hw, Finset.prod_empty, mul_one]
    | @insert i s hi ih =>
      intro b
      have hw : w (insert i s) = Function.update (w s) i (w s i ^ m) := by
        funext j
        by_cases hj : j = i
        · subst j
          simp only [w, Finset.mem_insert_self, ite_true, Function.update_self, hi, ite_false]
        · simp only [w, Finset.mem_insert, hj, false_or, Function.update_of_ne hj]
      have hi' : w s i = v i := ite_eq_right hi
      rw [hw, update_pow, ih, hi', Finset.prod_insert hi, mul_assoc]
  have hw : w Finset.univ = fun i => v i ^ m := by
    funext i
    simp only [w, Finset.mem_univ, ite_true]
  exact hw ▸ hs Finset.univ a

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormPowers.PDFormPowers
