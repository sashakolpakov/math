import OAI.NumberTheory.PadicHodge.GeometricComparison.SemilinearCharpolyTo
import OAI.NumberTheory.PadicHodge.GeometricComparison.FiltrationTransportT

/-! # Semilinear Filtration T -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SemilinearFiltrationT.SemilinearFiltration

noncomputable section

/-! Actual filtered subspaces and Hodge numbers transport across an equivalence of scalar fields. -/

variable {R S V W : Type*} [Field R] [Field S] (σ : R ≃+* S)
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W]

def map (e : V ≃ₛₗ[σ.toRingHom] W) (F : Linear.FiniteFiltration R V) : Linear.FiniteFiltration S W where
  step i := (F.step i).map e.toLinearMap
  antitone_step _ _ hij := Submodule.map_mono (F.antitone_step hij)
  eventually_top := by
    obtain ⟨i, hi⟩ := F.eventually_top
    refine ⟨i, ?_⟩
    rw [hi, Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]
  eventually_bot := by
    obtain ⟨i, hi⟩ := F.eventually_bot
    exact ⟨i, by simp only [hi, Submodule.map_bot]⟩

theorem finrank [FiniteDimensional R V] (e : V ≃ₛₗ[σ.toRingHom] W) :
    Module.finrank S W = Module.finrank R V := by
  simpa only [Fintype.card_fin] using
    Module.finrank_eq_card_basis (SemilinearCharpolyTo.SemilinearCharpoly.basis σ (Module.finBasis R V) e)

variable [FiniteDimensional R V] [FiniteDimensional S W]

omit [FiniteDimensional S W] in
theorem step_finrank (e : V ≃ₛₗ[σ.toRingHom] W) (F : Linear.FiniteFiltration R V) (i : ℤ) :
    Module.finrank S ((SemilinearFiltration.map σ e F).step i) = Module.finrank R (F.step i) :=
  SemilinearFiltration.finrank σ (e.submoduleMap (F.step i))

theorem tH_map (e : V ≃ₛₗ[σ.toRingHom] W) (F : Linear.FiniteFiltration R V) :
    (SemilinearFiltration.map σ e F).tH = F.tH := by
  unfold WeakAdmissibility.FilteredRepresentations.Construction.FiniteFiltration.tH
  congr 1
  funext i
  rw [(SemilinearFiltration.map σ e F).graded_finrank_eq_sub, F.graded_finrank_eq_sub, step_finrank, step_finrank]

omit [FiniteDimensional R V] [FiniteDimensional S W] in
theorem map_restrict_step (e : V ≃ₛₗ[σ.toRingHom] W) (F : Linear.FiniteFiltration R V)
    (P : Submodule R V) (i : ℤ) :
    ((F.restrict P).step i).map (e.submoduleMap P).toLinearMap =
      ((SemilinearFiltration.map σ e F).restrict (P.map e.toLinearMap)).step i := by
  ext x
  rw [Submodule.mem_map_equiv]
  change ((e.submoduleMap P).symm x : V) ∈ F.step i ↔
    (x : W) ∈ (F.step i).map e.toLinearMap
  rw [LinearEquiv.submoduleMap_symm_apply, Submodule.mem_map_equiv]

theorem tH_restrict_map (e : V ≃ₛₗ[σ.toRingHom] W) (F : Linear.FiniteFiltration R V)
    (P : Submodule R V) :
    ((SemilinearFiltration.map σ e F).restrict (P.map e.toLinearMap)).tH = (F.restrict P).tH := by
  have h := tH_map σ (e.submoduleMap P) (F.restrict P)
  have heq := FiltrationTransportT.FiltrationTransport.tH_eq_of_steps (SemilinearFiltration.map σ (e.submoduleMap P) (F.restrict P))
    ((SemilinearFiltration.map σ e F).restrict (P.map e.toLinearMap)) (map_restrict_step σ e F P)
  exact heq.symm.trans h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SemilinearFiltrationT.SemilinearFiltration
