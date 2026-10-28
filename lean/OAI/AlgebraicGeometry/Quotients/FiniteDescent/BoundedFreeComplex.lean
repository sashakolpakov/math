import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BoundedFlatModel

/-! # Bounded Free Complex -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent

noncomputable section

/-! A bounded flat complex with finite cohomology over a Noetherian local
ring admits a bounded finite free model, valid after every tensor base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {C : CochainComplex (ModuleCat.{u} R) ℕ} (M : CochainModel.Construction.CochainFiniteModel.Model C)

theorem CochainModel.Construction.CochainFiniteModel.Model.first_finite [Module.Finite R (C.homology 0)] :
    Module.Finite R (M.complex.X 0) := by
  have := M.quasiIso
  have : Module.Finite R (M.complex.homology 0) :=
    Module.Finite.equiv (isoOfQuasiIsoAt M.comparison 0).symm.toLinearEquiv
  have : Module.Finite R (M.complex.cycles 0) :=
    Module.Finite.equiv M.complex.isoHomologyπ₀.symm.toLinearEquiv
  have : Module.Finite R (M.complex.d 0 1).hom.ker :=
    Module.Finite.equiv (CochainZero.Construction.CochainZeroCycles.cyclesIso M.complex).toLinearEquiv
  have : Module.Finite R (M.complex.X 1) := M.finite 0
  exact SheafCohomology.Projective.FiniteHomologySequence.finite_of_exact (M.complex.d 0 1).hom.ker.subtype
    (M.complex.d 0 1).hom (LinearMap.exact_subtype_ker_map _)

theorem CochainModel.Construction.CochainFiniteModel.Model.first_free [IsLocalRing R] [Module.Finite R (C.homology 0)] :
    Module.Free R (M.complex.X 0) := by
  have := M.first_finite
  have := M.flat 0
  exact Module.free_of_flat_of_isLocalRing

theorem BoundedFreeComplex.Construction.CochainFiniteModel.exists_finite_free_complex [IsLocalRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hbound : ∃ N, ∀ q, N ≤ q → IsZero (C.X q))
    (hflat : ∀ q, Module.Flat R (C.X q))
    (hfinite : ∀ q, Module.Finite R (C.homology q)) :
    ∃ (D : CochainComplex (ModuleCat.{u} R) ℕ) (φ : D ⟶ C),
      QuasiIso φ ∧
      (∃ N, ∀ q, N ≤ q → IsZero (D.X q)) ∧
      (∀ q, Module.Finite R (D.X q)) ∧
      (∀ q, Module.Free R (D.X q)) ∧
      (∀ (A : Type u) [AddCommGroup A] [Module R A],
        QuasiIso (ModuleTensor.Construction.ModuleTensorFunctor.map A φ)) := by
  obtain ⟨N, hN⟩ := hbound
  obtain ⟨M⟩ := BoundedFlatModel.Construction.CochainFiniteModel.exists_model C N hN hflat (fun q => hfinite (q + 1))
  have := hfinite 0
  refine ⟨M.complex, M.comparison, M.quasiIso, M.bounded, ?_, ?_, M.tensor_quasiIso⟩
  · intro q
    cases q with
    | zero => exact M.first_finite
    | succ q => exact M.finite q
  · intro q
    cases q with
    | zero => exact M.first_free
    | succ q => exact M.free q

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent
