import OAI.NumberTheory.PadicHodge.PeriodInvariants.WittFiniteBasis

/-! # Lifted Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.LiftedBasis

noncomputable section

/-! The existing finite Witt basis consists of actual Teichmüller lifts and respects algebra maps. -/

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra

variable (p : ℕ) [Fact p.Prime] {A B ι : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [CharP A p] [PerfectRing A p] [CharP B p] [PerfectRing B p] [Fintype ι]
  (b : Module.Basis ι A B)

theorem apply_basis (i : ι) : PeriodInvariants.WittFiniteBasis.basis p b i = WittVector.teichmuller p (b i) := by
  classical
  rw [PeriodInvariants.WittFiniteBasis.basis, Module.Basis.coe_ofEquivFun]
  change Fintype.linearCombination (WittVector p A) (fun j => WittVector.teichmuller p (b j))
    (Pi.single i 1) = _
  rw [Fintype.linearCombination_apply_single, one_smul]

variable {C : Type*} [CommRing C] [Algebra A C] (f : B →ₐ[A] C)

theorem map_basis (i : ι) :
    PeriodInvariants.WittAlgebraFunctor.map p A f (PeriodInvariants.WittFiniteBasis.basis p b i) = WittVector.teichmuller p (f (b i)) := by
  rw [apply_basis]
  exact WittVector.map_teichmuller p f.toRingHom (b i)

omit C [CommRing C] [Algebra A C] f in
theorem map_basis_perm (f : B →ₐ[A] B) (σ : Equiv.Perm ι) (h : ∀ i, f (b i) = b (σ i)) (i : ι) :
    PeriodInvariants.WittAlgebraFunctor.map p A f (PeriodInvariants.WittFiniteBasis.basis p b i) = PeriodInvariants.WittFiniteBasis.basis p b (σ i) := by
  rw [map_basis, h, apply_basis]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.LiftedBasis
