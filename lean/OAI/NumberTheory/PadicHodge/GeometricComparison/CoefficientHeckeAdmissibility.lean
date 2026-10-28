import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeProjection
import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeSummandStability

/-! # Coefficient Hecke Admissibility -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientHeckeAdmissibility.GeneralizedHecke

noncomputable section

/-! Generalized coefficient eigenspaces inherit weak admissibility with every rational stable subspace tested. -/

variable {q : ℕ} [Fact q.Prime]
  {L V I : Type*} [Field L] [Algebra ℚ_[q] L]
  [AddCommGroup V] [Module L V] [Module ℚ_[q] V] [IsScalarTower ℚ_[q] L V]
  [FiniteDimensional L V] [FiniteDimensional ℚ_[q] V]

local instance coefficientSubspaceFinite (S : Submodule L V) : FiniteDimensional ℚ_[q] S :=
  Module.Finite.of_injective (S.subtype.restrictScalars ℚ_[q]) S.subtype_injective

omit [FiniteDimensional L V] [FiniteDimensional ℚ_[q] V] in
theorem restrictScalarFiltration_restrict (F : Linear.FiniteFiltration L V) (S : Submodule L V) :
    Linear.restrictScalarFiltration (K := ℚ_[q]) L (F.restrict S) =
      (Linear.restrictScalarFiltration (K := ℚ_[q]) L F).restrict (S.restrictScalars ℚ_[q]) := rfl

theorem coefficient_weaklyAdmissible_summand (F : Linear.FiniteFiltration L V)
    (φ : V ≃ₗ[L] V) (h : Linear.WeaklyAdmissible q (Linear.restrictScalarFiltration L F) (φ.restrictScalars ℚ_[q]))
    (T : I → Module.End L V) (χ : I → L)
    (hpair : ∀ i j, Commute (T i) (T j))
    (hcomm : ∀ i, Commute (T i) φ.toLinearMap)
    (hFil : ∀ i j, F.step j ≤ (F.step j).comap (T i)) :
    Linear.WeaklyAdmissible q (Linear.restrictScalarFiltration L (F.restrict (Linear.generalizedHeckeSummand T χ)))
      ((HeckeSummandStability.GeneralizedHecke.restriction φ T χ hcomm).restrictScalars ℚ_[q]) := by
  obtain ⟨P, hP, hPrange, hPcomm, hPpres⟩ := HeckeProjection.GeneralizedHecke.simultaneous_projection T χ hpair
  let S := Linear.generalizedHeckeSummand T χ
  have hc : IsCompl (S.restrictScalars ℚ_[q]) (P.ker.restrictScalars ℚ_[q]) := by
    apply (Submodule.isCompl_restrictScalars_iff ℚ_[q]).mpr
    rw [show S = P.range from hPrange.symm]
    exact LinearMap.IsIdempotentElem.isCompl hP
  have hS : S.restrictScalars ℚ_[q] ≤ (S.restrictScalars ℚ_[q]).comap
      (φ.restrictScalars ℚ_[q]).toLinearMap := HeckeSummandStability.GeneralizedHecke.summand_stable φ T χ hcomm
  have hK : P.ker.restrictScalars ℚ_[q] ≤ (P.ker.restrictScalars ℚ_[q]).comap
      (φ.restrictScalars ℚ_[q]).toLinearMap :=
    FilteredProjection.GeometricComparison.FiltrationTransport.commuting_kernel_stable P φ.toLinearMap (hPcomm φ.toLinearMap hcomm)
  rw [restrictScalarFiltration_restrict]
  apply WeakAdmissibilitySplit.weaklyAdmissible_split (Linear.restrictScalarFiltration L F) (φ.restrictScalars ℚ_[q]) h
    (S.restrictScalars ℚ_[q]) (P.ker.restrictScalars ℚ_[q]) hc hS hK
    _ ((HeckeSummandStability.GeneralizedHecke.restriction φ T χ hcomm).restrictScalars ℚ_[q]) rfl
  intro j
  have hs := FilteredProjection.GeometricComparison.FiltrationTransport.projection_splits_step F P hP j
    (hPpres (F.step j) (fun i => hFil i j))
  rw [hPrange] at hs
  have hr := congrArg (fun U : Submodule L V => U.restrictScalars ℚ_[q]) hs
  simpa only [Submodule.restrictScalars_sup, Submodule.restrictScalars_inf,
    Linear.restrictScalarFiltration, S] using hr

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientHeckeAdmissibility.GeneralizedHecke
