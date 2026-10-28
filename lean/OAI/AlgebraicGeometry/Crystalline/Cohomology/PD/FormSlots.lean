import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms

/-! # Form Slots -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormSlots.PDFormSlots

noncomputable section

/-!
# A differential-form slot is a divided-power derivation

Fixing all other factors of a differential symbol gives a derivation in
the remaining slot. This connects the universal one-form calculation to
higher-degree forms without assuming an exterior-power presentation.
-/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (δ : DividedPowers I)
  {n : ℕ} (v : Fin n → A) (i : Fin n)

def linearMap : A →ₗ[R] DeRham.PDDeRham.Form R A I δ n :=
  ((DeRham.PDDeRham.relations R A I δ n).mkQ.restrictScalars R).comp
    ((DeRhamPresentationTo.DeRhamPresentation.symbols R A n).toMultilinearMap.toLinearMap v i)

@[simp] theorem linearMap_apply (a : A) :
    linearMap R A I δ v i a = DeRham.PDDeRham.symbol R A I δ 1 (Function.update v i a) := rfl

/-- A differential symbol is a PD derivation in each fixed slot. -/
def derivation : Derivation R A (DeRham.PDDeRham.Form R A I δ n) where
  __ := linearMap R A I δ v i
  map_one_eq_zero' := by
    have h := congrArg (DeRham.PDDeRham.relations R A I δ n).mkQ
      (DeRhamPresentationTo.DeRhamPresentation.symbol_update_base R A v i 1)
    simp only [map_one, map_zero] at h
    exact h
  leibniz' a b := by
    have h := congrArg (DeRham.PDDeRham.relations R A I δ n).mkQ
      (DeRhamPresentationTo.DeRhamPresentation.symbol_update_mul R A v i a b)
    simp only [map_add, map_smul] at h
    exact h

@[simp] theorem derivation_apply (a : A) :
    derivation R A I δ v i a = DeRham.PDDeRham.symbol R A I δ 1 (Function.update v i a) := rfl

theorem derivation_dpow (m : ℕ) {x : A} (hx : x ∈ I) :
    derivation R A I δ v i (δ.dpow (m + 1) x) = δ.dpow m x • derivation R A I δ v i x :=
  DeRham.PDDeRham.symbol_update_dpow R A I δ v i ⟨x, hx⟩ m

/-- Vanishing on differential symbols implies vanishing of the whole form module. -/
theorem eq_zero_of_symbols (hz : ∀ v : Fin n → A, DeRham.PDDeRham.symbol R A I δ 1 v = 0)
    (ω : DeRham.PDDeRham.Form R A I δ n) : ω = 0 := by
  obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective (DeRham.PDDeRham.relations R A I δ n) ω
  obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective (DeRhamPresentationTo.DeRhamPresentation.relations R A n) ω
  induction ω using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | single v a =>
    change DeRham.PDDeRham.symbol R A I δ a v = 0
    rw [DeRham.PDDeRham.symbol_smul_one, hz, smul_zero]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormSlots.PDFormSlots
