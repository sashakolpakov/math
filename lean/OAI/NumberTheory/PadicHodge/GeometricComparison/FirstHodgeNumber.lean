import OAI.NumberTheory.PadicHodge.GeometricComparison.FiltrationTransportT

/-! # First Hodge Number -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FirstHodgeNumber.FiltrationTransport

noncomputable section

/-! For filtrations in degrees zero and one, the Hodge number is the dimension of the first step. -/

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  [FiniteDimensional K V] [FiniteDimensional K W]

theorem tH_h1 (F : Linear.FiniteFiltration K V) (h0 : F.step 0 = ⊤) (h2 : F.step 2 = ⊥) :
    F.tH = Module.finrank K (F.step 1) := by
  unfold WeakAdmissibility.FilteredRepresentations.Construction.FiniteFiltration.tH
  rw [finsum_eq_single _ (1 : ℤ) (by
    intro i hi
    by_cases hzero : i = 0
    · simp [hzero]
    · rcases lt_or_ge i 0 with hneg | hnonneg
      · rw [F.graded_finrank_eq_zero_of_lt h0 hneg, Nat.cast_zero, mul_zero]
      · rw [F.graded_finrank_eq_zero_of_le h2 (by omega), Nat.cast_zero, mul_zero])]
  rw [Int.cast_one, one_mul, F.graded_finrank_eq_sub]
  erw [h2, finrank_bot, Nat.sub_zero]

theorem h1_tH_le_of_injective (F : Linear.FiniteFiltration K V) (G : Linear.FiniteFiltration K W)
    (hF0 : F.step 0 = ⊤) (hF2 : F.step 2 = ⊥)
    (hG0 : G.step 0 = ⊤) (hG2 : G.step 2 = ⊥)
    (f : V →ₗ[K] W) (hinj : Function.Injective f)
    (hFil : (F.step 1).map f ≤ G.step 1) : F.tH ≤ G.tH := by
  rw [tH_h1 F hF0 hF2, tH_h1 G hG0 hG2]
  exact_mod_cast (show Module.finrank K (F.step 1) ≤ Module.finrank K (G.step 1) from
    LinearMap.finrank_le_finrank_of_injective (f :=
      (f.domRestrict (F.step 1)).codRestrict (G.step 1)
        (fun x => hFil ⟨x, x.property, rfl⟩)) (by
          intro x y hxy
          apply Subtype.ext
          exact hinj (congrArg Subtype.val hxy)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FirstHodgeNumber.FiltrationTransport
