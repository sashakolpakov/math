import OAI.NumberTheory.PadicHodge.GeometricComparison.Linear

/-! # Filtration Transport T -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FiltrationTransportT.FiltrationTransport

noncomputable section

/-! Transport of bounded filtrations and their actual associated-graded dimensions. -/

universe u v w
variable {R : Type u} [Field R]
  {D : Type v} [AddCommGroup D] [Module R D]
  {E : Type w} [AddCommGroup E] [Module R E]

/-- Image filtration under a specified equivalence. -/
def map (e : D ≃ₗ[R] E) (F : Linear.FiniteFiltration R D) : Linear.FiniteFiltration R E where
  step i := (F.step i).map e.toLinearMap
  antitone_step _ _ hij := Submodule.map_mono (F.antitone_step hij)
  eventually_top := by
    obtain ⟨i, hi⟩ := F.eventually_top
    refine ⟨i, ?_⟩
    rw [hi, Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]
  eventually_bot := by
    obtain ⟨i, hi⟩ := F.eventually_bot
    exact ⟨i, by simp [hi]⟩

theorem map_step (e : D ≃ₗ[R] E) (F : Linear.FiniteFiltration R D) (i : ℤ) :
    (FiltrationTransport.map e F).step i = (F.step i).map e.toLinearMap := rfl

theorem map_restrict_step (e : D ≃ₗ[R] E) (F : Linear.FiniteFiltration R D)
    (S : Submodule R D) (i : ℤ) :
    ((F.restrict S).step i).map (e.submoduleMap S).toLinearMap =
      ((FiltrationTransport.map e F).restrict (S.map e.toLinearMap)).step i := by
  ext x
  rw [Submodule.mem_map_equiv]
  change ((e.submoduleMap S).symm x : D) ∈ F.step i ↔
    (x : E) ∈ (F.step i).map e.toLinearMap
  rw [LinearEquiv.submoduleMap_symm_apply, Submodule.mem_map_equiv]

variable [FiniteDimensional R D] [FiniteDimensional R E]

omit [FiniteDimensional R D] [FiniteDimensional R E] in
theorem step_finrank (e : D ≃ₗ[R] E) (F : Linear.FiniteFiltration R D) (i : ℤ) :
    Module.finrank R ((FiltrationTransport.map e F).step i) = Module.finrank R (F.step i) :=
  (e.submoduleMap (F.step i)).finrank_eq.symm

theorem graded_finrank (e : D ≃ₗ[R] E) (F : Linear.FiniteFiltration R D) (i : ℤ) :
    Module.finrank R ((FiltrationTransport.map e F).Graded i) = Module.finrank R (F.Graded i) := by
  rw [(FiltrationTransport.map e F).graded_finrank_eq_sub, F.graded_finrank_eq_sub,
    step_finrank, step_finrank]

theorem tH_map (e : D ≃ₗ[R] E) (F : Linear.FiniteFiltration R D) : (FiltrationTransport.map e F).tH = F.tH := by
  unfold WeakAdmissibility.FilteredRepresentations.Construction.FiniteFiltration.tH
  congr 1
  funext i
  rw [graded_finrank]

theorem tH_eq_of_steps (F G : Linear.FiniteFiltration R D)
    (h : ∀ i, F.step i = G.step i) : F.tH = G.tH := by
  unfold WeakAdmissibility.FilteredRepresentations.Construction.FiniteFiltration.tH
  congr 1
  funext i
  rw [F.graded_finrank_eq_sub, G.graded_finrank_eq_sub, h, h]

omit [FiniteDimensional R E] in
theorem tH_restrict_map (e : D ≃ₗ[R] E) (F : Linear.FiniteFiltration R D) (S : Submodule R D) :
    ((FiltrationTransport.map e F).restrict (S.map e.toLinearMap)).tH = (F.restrict S).tH := by
  have h := tH_eq_of_steps (FiltrationTransport.map (e.submoduleMap S) (F.restrict S))
    ((FiltrationTransport.map e F).restrict (S.map e.toLinearMap)) (map_restrict_step e F S)
  exact h.symm.trans (tH_map (e.submoduleMap S) (F.restrict S))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FiltrationTransportT.FiltrationTransport
