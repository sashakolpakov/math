import OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaDegreeZero

/-! # Scalar Nullhomotopy Eta -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ScalarNullhomotopyEta

/-! # Ordinary eta removes a scalar-null-homotopic torsion-free complex -/

open _root_.CategoryTheory OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaComplex OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaCycles OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaBoundaries OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaCohomology

universe u v
variable {R : Type u} [CommRing R] (a : R) (C : CochainComplex (ModuleCat.{v} R) ℕ)
  (h : ∀ n, C.X (n + 1) →ₗ[R] C.X n)
  (hzero : ∀ x, h 0 ((C.d 0 1).hom x) = a • x)
  (hsucc : ∀ n x, h (n + 1) ((C.d (n + 1) (n + 1 + 1)).hom x) +
    (C.d n (n + 1)).hom (h n x) = a • x)

include hsucc in
theorem scalar_cohomology_zero (n : ℕ) (x : EtaCohomology.cohomology C n) : a • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    change (Submodule.Quotient.mk (a • z) : EtaCohomology.cohomology C n) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨h n z.val, ?_⟩
    apply Subtype.ext
    have hz : (C.d (n + 1) (n + 1 + 1)).hom z.val = 0 := z.property
    have he := hsucc n z.val
    rw [hz, map_zero, zero_add] at he
    exact he

variable (ha : ∀ n, IsSMulRegular (C.X n) a)

include hsucc ha in
theorem eta_positive_zero (n : ℕ) (x : (EtaComplex.eta a C).homology (n + 1)) : x = 0 := by
  let e := (EtaConcreteHomology.Concrete.etaHomologyIso a C n).toLinearEquiv
  apply e.injective
  rw [map_zero]
  obtain ⟨y, hy⟩ := EtaCohomology.compare_surjective a C n (ha (n + 1)) (ha (n + 1 + 1)) (e x)
  exact hy.symm.trans ((EtaCohomology.compare_eq_zero_iff a C n (ha (n + 1)) y).mpr
    (scalar_cohomology_zero a C h hsucc n y))

include hzero ha in
theorem eta_zero_zero (x : (EtaComplex.eta a C).homology 0) : x = 0 := by
  let e := (EtaDegreeZero.homologyZeroEquiv a C).symm.trans
    (EtaDegreeZero.zeroHomologyCyclesEquiv C)
  apply e.injective
  rw [map_zero]
  apply Subtype.ext
  apply ha 0
  change a • (e x).val = a • (0 : C.X 0)
  have hz : (C.d 0 1).hom (e x).val = 0 := (e x).property
  have he := hzero (e x).val
  rw [hz, map_zero] at he
  exact he.symm.trans (smul_zero a).symm

include hzero hsucc ha in
theorem homology_subsingleton (n : ℕ) : Subsingleton ((EtaComplex.eta a C).homology n) := by
  have hz : ∀ x : (EtaComplex.eta a C).homology n, x = 0 := by
    cases n with
    | zero => exact eta_zero_zero a C h hzero ha
    | succ n => exact eta_positive_zero a C h hsucc ha n
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ScalarNullhomotopyEta
