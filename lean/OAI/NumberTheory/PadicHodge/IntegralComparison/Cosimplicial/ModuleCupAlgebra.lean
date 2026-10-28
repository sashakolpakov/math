import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ModuleCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.CupAlgebra

/-! # Module Cup Algebra -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ModuleCupAlgebra

noncomputable section

/-! Associativity, units, and alternating degree-one products on the
actual module cohomology of a cosimplicial commutative algebra. -/

open _root_.CategoryTheory
open scoped Simplicial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality
  ModuleComplex

universe u v

variable {R : Type u} [CommRing R] (A : CosimplicialObject (CommAlgCat.{v} R))

def cycleDegreeCast {m n : ℕ} (h : m = n) :
    Module.CochainClasses.cycles (ModuleComplex.complex A) m ≃ₗ[R] Module.CochainClasses.cycles (ModuleComplex.complex A) n := by
  subst n
  exact LinearEquiv.refl _ _

def cohomologyDegreeCast {m n : ℕ} (h : m = n) :
    (ModuleComplex.complex A).homology m ≃ₗ[R] (ModuleComplex.complex A).homology n := by
  subst n
  exact LinearEquiv.refl _ _

theorem cycleDegreeCast_val {m n : ℕ} (h : m = n) (x : Module.CochainClasses.cycles (ModuleComplex.complex A) m) :
    (cycleDegreeCast A h x).1 = CupDegrees.degreeCast (ModuleComplex.ringObject A) h x.1 := by
  subst n
  rfl

theorem cohomologyDegreeCast_class {m n : ℕ} (h : m = n) (x : Module.CochainClasses.cycles (ModuleComplex.complex A) m) :
    cohomologyDegreeCast A h (Module.CochainClasses.classMap (ModuleComplex.complex A) m x) =
      Module.CochainClasses.classMap (ModuleComplex.complex A) n (cycleDegreeCast A h x) := by
  subst n
  rfl

theorem cycleCup_assoc {p q r : ℕ} (x : Module.CochainClasses.cycles (ModuleComplex.complex A) p)
    (y : Module.CochainClasses.cycles (ModuleComplex.complex A) q) (z : Module.CochainClasses.cycles (ModuleComplex.complex A) r) :
    cycleDegreeCast A (Nat.add_assoc p q r)
        (ModuleCocycles.Cup.cycleCup A (p + q) r (ModuleCocycles.Cup.cycleCup A p q x y) z) =
      ModuleCocycles.Cup.cycleCup A p (q + r) x (ModuleCocycles.Cup.cycleCup A q r y z) := by
  apply Subtype.ext
  exact (cycleDegreeCast_val A _ _).trans
    (CupAlgebra.cup_assoc (ModuleComplex.ringObject A) x.1 y.1 z.1)

theorem cohomologyCup_assoc {p q r : ℕ} (x : (ModuleComplex.complex A).homology p)
    (y : (ModuleComplex.complex A).homology q) (z : (ModuleComplex.complex A).homology r) :
    cohomologyDegreeCast A (Nat.add_assoc p q r)
        (ModuleCup.cohomologyCup A (p + q) r (ModuleCup.cohomologyCup A p q x y) z) =
      ModuleCup.cohomologyCup A p (q + r) x (ModuleCup.cohomologyCup A q r y z) := by
  obtain ⟨cx, rfl⟩ := Module.CochainClasses.classMap_surjective (ModuleComplex.complex A) p x
  obtain ⟨cy, rfl⟩ := Module.CochainClasses.classMap_surjective (ModuleComplex.complex A) q y
  obtain ⟨cz, rfl⟩ := Module.CochainClasses.classMap_surjective (ModuleComplex.complex A) r z
  simp only [ModuleCup.cup_class, cohomologyDegreeCast_class, cycleCup_assoc]

def cycleOne : Module.CochainClasses.cycles (ModuleComplex.complex A) 0 :=
  ⟨(1 : A.obj ⦋0⦌), (ModuleComplex.complex_d_apply A 0 _).trans
    (CupAlgebra.differential_one_zero (ModuleComplex.ringObject A))⟩

def cohomologyOne : (ModuleComplex.complex A).homology 0 := Module.CochainClasses.classMap (ModuleComplex.complex A) 0 (cycleOne A)

theorem cycleOne_cup {p : ℕ} (x : Module.CochainClasses.cycles (ModuleComplex.complex A) p) :
    cycleDegreeCast A (Nat.zero_add p) (ModuleCocycles.Cup.cycleCup A 0 p (cycleOne A) x) = x := by
  apply Subtype.ext
  exact (cycleDegreeCast_val A _ _).trans (CupAlgebra.one_cup (ModuleComplex.ringObject A) x.1)

theorem cycleCup_one {p : ℕ} (x : Module.CochainClasses.cycles (ModuleComplex.complex A) p) :
    ModuleCocycles.Cup.cycleCup A p 0 x (cycleOne A) = x := by
  apply Subtype.ext
  exact CupAlgebra.cup_one (ModuleComplex.ringObject A) x.1

theorem cohomologyOne_cup {p : ℕ} (x : (ModuleComplex.complex A).homology p) :
    cohomologyDegreeCast A (Nat.zero_add p) (ModuleCup.cohomologyCup A 0 p (cohomologyOne A) x) = x := by
  obtain ⟨cx, rfl⟩ := Module.CochainClasses.classMap_surjective (ModuleComplex.complex A) p x
  change cohomologyDegreeCast A (Nat.zero_add p)
    (ModuleCup.cohomologyCup A 0 p (Module.CochainClasses.classMap (ModuleComplex.complex A) 0 (cycleOne A))
      (Module.CochainClasses.classMap (ModuleComplex.complex A) p cx)) = _
  rw [ModuleCup.cup_class, cohomologyDegreeCast_class, cycleOne_cup]

theorem cohomologyCup_one {p : ℕ} (x : (ModuleComplex.complex A).homology p) :
    ModuleCup.cohomologyCup A p 0 x (cohomologyOne A) = x := by
  obtain ⟨cx, rfl⟩ := Module.CochainClasses.classMap_surjective (ModuleComplex.complex A) p x
  change ModuleCup.cohomologyCup A p 0 (Module.CochainClasses.classMap (ModuleComplex.complex A) p cx)
    (Module.CochainClasses.classMap (ModuleComplex.complex A) 0 (cycleOne A)) = _
  rw [ModuleCup.cup_class, cycleCup_one]
  rfl

theorem cohomologyCup_anticomm [Invertible (2 : A.obj ⦋1⦌)]
    [Invertible (2 : A.obj ⦋2⦌)] (x y : (ModuleComplex.complex A).homology 1) :
    ModuleCup.cohomologyCup A 1 1 x y = -(ModuleCup.cohomologyCup A 1 1 y x) := by
  have h := ModuleCup.cup_self_eq_zero A (x + y)
  simp only [map_add, LinearMap.add_apply, ModuleCup.cup_self_eq_zero, zero_add, add_zero] at h
  exact eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using h)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ModuleCupAlgebra
