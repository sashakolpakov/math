import OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaConcreteHomology

/-! # Eta Degree Zero -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaDegreeZero

noncomputable section

/-!
# Eta in degree zero and the formula in every nonnegative degree

Degree-zero cycles are unchanged by eta. They have no scalar torsion
when the original degree-zero term has none. Combined with the positive
degree calculation, this gives the formula for actual homology in all
degrees of a nonnegative cochain complex.
-/

universe u v

open _root_.CategoryTheory OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaComplex OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaCycles OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaCohomology OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaConcreteHomology.Concrete

variable {R : Type u} [CommRing R] (a : R)

theorem etaCycles_eq (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    EtaCycles.cycles (EtaComplex.eta a C) n = EtaCycles.etaCycles a C n := by
  change LinearMap.ker ((EtaComplex.eta a C).d n (n + 1)).hom = LinearMap.ker (EtaComplex.differential a C n)
  rw [EtaComplex.eta_d]
  rfl

def etaCyclesEquiv (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    EtaCycles.cycles (EtaComplex.eta a C) n ≃ₗ[R] EtaCycles.etaCycles a C n where
  toFun x := ⟨x.val, by
    have hx : (EtaComplex.eta a C).d n (n + 1) x.val = 0 := x.property
    rw [EtaComplex.eta_d] at hx
    exact hx⟩
  invFun x := ⟨x.val, by
    change (EtaComplex.eta a C).d n (n + 1) x.val = 0
    rw [EtaComplex.eta_d]
    exact x.property⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_add' x y := Subtype.ext rfl
  map_smul' r x := Subtype.ext rfl

theorem scaleCycles_zero_bijective (C : CochainComplex (ModuleCat.{v} R) ℕ) :
    Function.Bijective (EtaCycles.scaleCycles a C 0) := by
  constructor
  · intro x y h
    apply Subtype.ext
    have h' := congrArg (fun z : EtaCycles.etaCycles a C 0 => (z.val : C.X 0)) h
    change a ^ 0 • (x : C.X 0) = a ^ 0 • (y : C.X 0) at h'
    simpa only [pow_zero, one_smul] using h'
  · intro x
    have hx : C.d 0 1 (x.val : C.X 0) = 0 :=
      congrArg (fun z : EtaComplex.term a C 1 => (z : C.X 1))
        (show EtaComplex.differential a C 0 x.val = 0 from x.property)
    refine ⟨⟨x.val, hx⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change a ^ 0 • (x.val : C.X 0) = (x.val : C.X 0)
    rw [pow_zero, one_smul]

def zeroCyclesIso (C : CochainComplex (ModuleCat.{v} R) ℕ) :
    C.cycles 0 ≅ ModuleCat.of R (EtaCycles.cycles C 0) :=
  C.cyclesIsoSc' 0 0 1 (by simp) (by simp) ≪≫ (C.sc' 0 0 1).moduleCatCyclesIso

def zeroHomologyCyclesEquiv (C : CochainComplex (ModuleCat.{v} R) ℕ) :
    C.homology 0 ≃ₗ[R] EtaCycles.cycles C 0 :=
  (C.isoHomologyπ₀.symm ≪≫ zeroCyclesIso C).toLinearEquiv

def homologyZeroEquiv (C : CochainComplex (ModuleCat.{v} R) ℕ) :
    C.homology 0 ≃ₗ[R] (EtaComplex.eta a C).homology 0 :=
  (zeroHomologyCyclesEquiv C).trans
    ((LinearEquiv.ofBijective (EtaCycles.scaleCycles a C 0) (scaleCycles_zero_bijective a C)).trans
      ((etaCyclesEquiv a C 0).symm.trans
        (zeroHomologyCyclesEquiv (EtaComplex.eta a C)).symm))

theorem zeroHomology_torsion_eq_bot (C : CochainComplex (ModuleCat.{v} R) ℕ)
    (ha : IsSMulRegular (C.X 0) a) : EtaCohomology.scalarTorsion a (C.homology 0) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hx' : a • x = 0 := hx
  have he : a • ((zeroHomologyCyclesEquiv C x : EtaCycles.cycles C 0) : C.X 0) = 0 := by
    have h := congrArg (fun z : C.homology 0 =>
      ((zeroHomologyCyclesEquiv C z : EtaCycles.cycles C 0) : C.X 0)) hx'
    simpa only [map_smul, map_zero, Submodule.coe_smul, ZeroMemClass.coe_zero] using h
  have he0 : zeroHomologyCyclesEquiv C x = 0 := by
    apply Subtype.ext
    apply ha
    change a • ((zeroHomologyCyclesEquiv C x : EtaCycles.cycles C 0) : C.X 0) = a • (0 : C.X 0)
    rw [he, smul_zero]
  change x = 0
  exact (zeroHomologyCyclesEquiv C).injective (he0.trans (map_zero _).symm)

def homologyZeroTorsionEquiv (C : CochainComplex (ModuleCat.{v} R) ℕ)
    (ha : IsSMulRegular (C.X 0) a) :
    (C.homology 0 ⧸ EtaCohomology.scalarTorsion a (C.homology 0)) ≃ₗ[R] (EtaComplex.eta a C).homology 0 :=
  ((EtaCohomology.scalarTorsion a (C.homology 0)).quotEquivOfEqBot (zeroHomology_torsion_eq_bot a C ha)).trans
    (homologyZeroEquiv a C)

def homologyTorsionEquivAll (C : CochainComplex (ModuleCat.{v} R) ℕ)
    (ha : ∀ n, IsSMulRegular (C.X n) a) (n : ℕ) :
    (C.homology n ⧸ EtaCohomology.scalarTorsion a (C.homology n)) ≃ₗ[R] (EtaComplex.eta a C).homology n := by
  cases n with
  | zero => exact homologyZeroTorsionEquiv a C (ha 0)
  | succ n => exact EtaConcreteHomology.Concrete.homologyTorsionEquiv a C n (ha (n + 1)) (ha (n + 1 + 1))

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaDegreeZero
