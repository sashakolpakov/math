import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.LiftedBasis
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Base Change Naturality -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.Witt.BaseChangeNaturality.Finite

/-! Actual Witt vectors commute with finite free perfect base change, through their canonical tensor map. -/

open scoped TensorProduct

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra

variable (p : ℕ) [Fact p.Prime]

abbrev tower (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] :
    IsScalarTower (WittVector p R) (WittVector p S) (WittVector p T) :=
  IsScalarTower.of_algebraMap_eq (fun w => by
    apply WittVector.ext
    intro n
    exact IsScalarTower.algebraMap_apply R S T (w.coeff n))

attribute [local instance] tower

variable (R S A : Type*) [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]

def map : (WittVector p S) ⊗[WittVector p R] (WittVector p A) →ₐ[WittVector p S]
    WittVector p (S ⊗[R] A) :=
  Algebra.TensorProduct.lift (Algebra.ofId (WittVector p S) (WittVector p (S ⊗[R] A)))
    (PeriodInvariants.WittAlgebraFunctor.map p R (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A))
    (fun _ _ => Commute.all _ _)

theorem map_tmul (s : WittVector p S) (w : WittVector p A) :
    Finite.map p R S A (s ⊗ₜ[WittVector p R] w) =
      WittVector.map (algebraMap S (S ⊗[R] A)) s *
        WittVector.map (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom w := rfl

variable [CharP R p] [PerfectRing R p] [CharP S p] [PerfectRing S p]
  [CharP A p] [PerfectRing A p] [CharP (S ⊗[R] A) p] [PerfectRing (S ⊗[R] A) p]
  {ι : Type*} [Fintype ι] (b : Module.Basis ι R A)

theorem map_basis (i : ι) :
    Finite.map p R S A (((PeriodInvariants.WittFiniteBasis.basis p b).baseChange (WittVector p S)) i) =
      PeriodInvariants.WittFiniteBasis.basis p (b.baseChange S) i := by
  rw [Module.Basis.baseChange_apply, LiftedBasis.apply_basis, map_tmul, map_one, one_mul,
    WittVector.map_teichmuller, LiftedBasis.apply_basis, Module.Basis.baseChange_apply]
  rfl

def linearEquiv : (WittVector p S) ⊗[WittVector p R] (WittVector p A) ≃ₗ[WittVector p S]
    WittVector p (S ⊗[R] A) :=
  ((PeriodInvariants.WittFiniteBasis.basis p b).baseChange (WittVector p S)).equiv
    (PeriodInvariants.WittFiniteBasis.basis p (b.baseChange S)) (Equiv.refl ι)

theorem map_eq : (Finite.map p R S A).toLinearMap = (linearEquiv p R S A b).toLinearMap := by
  apply ((PeriodInvariants.WittFiniteBasis.basis p b).baseChange (WittVector p S)).ext
  intro i
  exact (map_basis p R S A b i).trans
    (((PeriodInvariants.WittFiniteBasis.basis p b).baseChange (WittVector p S)).equiv_apply
      i (PeriodInvariants.WittFiniteBasis.basis p (b.baseChange S)) (Equiv.refl ι)).symm

def equiv : (WittVector p S) ⊗[WittVector p R] (WittVector p A) ≃ₐ[WittVector p S]
    WittVector p (S ⊗[R] A) :=
  AlgEquiv.ofBijective (Finite.map p R S A) (by
    change Function.Bijective (Finite.map p R S A).toLinearMap
    rw [map_eq p R S A b]
    exact (linearEquiv p R S A b).bijective)

end NumberTheory.PadicHodge.IntegralComparison.Witt.BaseChangeNaturality.Finite

namespace NumberTheory.PadicHodge.IntegralComparison.Witt.BaseChangeNaturality

/-! The canonical Witt tensor base-change map commutes with actual algebra endomorphisms. -/

open scoped TensorProduct

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra Finite.tower

variable (p : ℕ) [Fact p.Prime] (R S A : Type*) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] (f : A →ₐ[R] A)

def tensorMap : S ⊗[R] A →ₐ[S] S ⊗[R] A := Algebra.TensorProduct.map (AlgHom.id S S) f

theorem right (w : WittVector p A) :
    PeriodInvariants.WittAlgebraFunctor.map p S (tensorMap R S A f)
      (WittVector.map (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom w) =
        WittVector.map (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom
          (PeriodInvariants.WittAlgebraFunctor.map p R f w) := by
  apply WittVector.ext
  intro n
  rfl

theorem natural (z : (WittVector p S) ⊗[WittVector p R] (WittVector p A)) :
    Finite.map p R S A ((PeriodInvariants.WittAlgebraFunctor.map p R f).toLinearMap.baseChange (WittVector p S) z) =
      PeriodInvariants.WittAlgebraFunctor.map p S (tensorMap R S A f) (Finite.map p R S A z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s w =>
    rw [LinearMap.baseChange_tmul, Finite.map_tmul, Finite.map_tmul, map_mul]
    have hleft := (PeriodInvariants.WittAlgebraFunctor.map p S (tensorMap R S A f)).commutes s
    change PeriodInvariants.WittAlgebraFunctor.map p S (tensorMap R S A f)
      (WittVector.map (algebraMap S (S ⊗[R] A)) s) = WittVector.map (algebraMap S (S ⊗[R] A)) s at hleft
    rw [hleft, right]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end NumberTheory.PadicHodge.IntegralComparison.Witt.BaseChangeNaturality

end

end OAI
