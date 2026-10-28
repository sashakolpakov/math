import OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilityTransport

/-! # Nested Filtration -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.NestedFiltration.FiltrationTransport

/-! Induced filtrations and stable operators agree under the actual inclusion of a subspace of a subspace. -/

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem nested_restrict_step (F : Linear.FiniteFiltration K V) (S : Submodule K V)
    (U : Submodule K S) (i : ℤ) :
    (((F.restrict S).restrict U).step i).map (S.equivSubtypeMap U).toLinearMap =
      (F.restrict (U.map S.subtype)).step i := by
  ext x
  rw [Submodule.mem_map_equiv]
  change (((S.equivSubtypeMap U).symm x : U) : V) ∈ F.step i ↔
    (x : V) ∈ F.step i
  rfl

theorem nested_restrict_tH [FiniteDimensional K V] (F : Linear.FiniteFiltration K V)
    (S : Submodule K V) (U : Submodule K S) :
    ((F.restrict S).restrict U).tH = (F.restrict (U.map S.subtype)).tH := by
  exact (FiltrationTransportT.FiltrationTransport.tH_map (S.equivSubtypeMap U) ((F.restrict S).restrict U)).symm.trans
    (FiltrationTransportT.FiltrationTransport.tH_eq_of_steps _ _ (nested_restrict_step F S U))

theorem nested_stable (T : Module.End K V) (S : Submodule K V)
    (hS : S ≤ S.comap T) (U : Submodule K S)
    (hU : U ≤ U.comap (T.restrict hS)) :
    U.map S.subtype ≤ (U.map S.subtype).comap T := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨T.restrict hS y, hU hy, rfl⟩

theorem nested_restrict_det (T : Module.End K V) (S : Submodule K V)
    (hS : S ≤ S.comap T) (U : Submodule K S)
    (hU : U ≤ U.comap (T.restrict hS)) :
    ((T.restrict hS).restrict hU).det =
      (T.restrict (nested_stable T S hS U hU)).det := by
  exact (WeakAdmissibilityTransport.FiltrationTransport.det_eq_of_intertwines (S.equivSubtypeMap U) _ _ (fun _ => rfl)).symm

end NumberTheory.PadicHodge.GeometricComparison.NestedFiltration.FiltrationTransport

namespace NumberTheory.PadicHodge.GeometricComparison.NestedFiltration

/-! All stable-subspace inequalities are inherited by an actual invariant subspace. -/

variable {q : ℕ} [Fact q.Prime]
  {V : Type*} [AddCommGroup V] [Module ℚ_[q] V] [FiniteDimensional ℚ_[q] V]

theorem weaklyAdmissible_restrict_iff (F : Linear.FiniteFiltration ℚ_[q] V)
    (φ : V ≃ₗ[ℚ_[q]] V) (h : Linear.WeaklyAdmissible q F φ)
    (S : Submodule ℚ_[q] V) (hS : S ≤ S.comap φ.toLinearMap)
    (ψ : S ≃ₗ[ℚ_[q]] S) (hψ : ψ.toLinearMap = φ.toLinearMap.restrict hS) :
    Linear.WeaklyAdmissible q (F.restrict S) ψ ↔
      (F.restrict S).tH = (Padic.valuation ψ.toLinearMap.det : ℚ) := by
  constructor
  · exact And.left
  · intro heq
    refine ⟨heq, ?_⟩
    simp only [hψ]
    intro U hU
    rw [FiltrationTransport.nested_restrict_tH,
      FiltrationTransport.nested_restrict_det]
    exact h.2 (U.map S.subtype)
      (FiltrationTransport.nested_stable φ.toLinearMap S hS U hU)

end NumberTheory.PadicHodge.GeometricComparison.NestedFiltration

end

end OAI
