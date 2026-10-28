import OAI.NumberTheory.PadicHodge.GeometricComparison.FiltrationTransportT

/-! # Split Filtration -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SplitFiltration.FiltrationTransport

noncomputable section

/-! Hodge numbers add for complementary subspaces that split each actual filtration step. -/

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem restrict_step_finrank (F : Linear.FiniteFiltration K V) (S : Submodule K V) (i : ℤ) :
    Module.finrank K ((F.restrict S).step i) =
      Module.finrank K (S ⊓ F.step i : Submodule K V) := by
  have h := (S.equivSubtypeMap ((F.restrict S).step i)).finrank_eq
  change Module.finrank K ((F.step i).comap S.subtype) =
    Module.finrank K (((F.step i).comap S.subtype).map S.subtype) at h
  erw [Submodule.map_comap_subtype] at h
  exact h

theorem split_step_finrank (F : Linear.FiniteFiltration K V) (S T : Submodule K V)
    (hd : Disjoint S T) (i : ℤ)
    (hsplit : (S ⊓ F.step i) ⊔ (T ⊓ F.step i) = F.step i) :
    Module.finrank K ((F.restrict S).step i) +
      Module.finrank K ((F.restrict T).step i) = Module.finrank K (F.step i) := by
  rw [restrict_step_finrank, restrict_step_finrank]
  have hi : Disjoint (S ⊓ F.step i) (T ⊓ F.step i) := hd.mono inf_le_left inf_le_left
  have h := Submodule.finrank_sup_add_finrank_inf_eq (S ⊓ F.step i) (T ⊓ F.step i)
  erw [hsplit, hi.eq_bot, finrank_bot, add_zero] at h
  exact h.symm

theorem split_graded_finrank (F : Linear.FiniteFiltration K V) (S T : Submodule K V)
    (hd : Disjoint S T)
    (hsplit : ∀ i, (S ⊓ F.step i) ⊔ (T ⊓ F.step i) = F.step i) (i : ℤ) :
    Module.finrank K ((F.restrict S).Graded i) +
      Module.finrank K ((F.restrict T).Graded i) = Module.finrank K (F.Graded i) := by
  have h₀ := split_step_finrank F S T hd i (hsplit i)
  have h₁ := split_step_finrank F S T hd (i + 1) (hsplit (i + 1))
  have h₂ := (F.restrict S).graded_finrank_add i
  have h₃ := (F.restrict T).graded_finrank_add i
  have h₄ := F.graded_finrank_add i
  omega

theorem split_tH (F : Linear.FiniteFiltration K V) (S T : Submodule K V)
    (hd : Disjoint S T)
    (hsplit : ∀ i, (S ⊓ F.step i) ⊔ (T ⊓ F.step i) = F.step i) :
    (F.restrict S).tH + (F.restrict T).tH = F.tH := by
  unfold WeakAdmissibility.FilteredRepresentations.Construction.FiniteFiltration.tH
  rw [← finsum_add_distrib (F.restrict S).hodge_summand_finite_support
    (F.restrict T).hodge_summand_finite_support]
  congr 1
  funext i
  rw [← mul_add, ← Nat.cast_add, split_graded_finrank F S T hd hsplit i]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SplitFiltration.FiltrationTransport
