import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ModuleCocycles
import OAI.NumberTheory.PadicHodge.IntegralComparison.BilinearQuotient
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.OneCupBoundary

/-! # Module Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ModuleCup

noncomputable section

/-! The coefficient-linear Alexander–Whitney product on the original
module cohomology of a cosimplicial commutative algebra. -/

open _root_.CategoryTheory
open scoped Simplicial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality
  ModuleComplex

universe u v

variable {R : Type u} [CommRing R] (A : CosimplicialObject (CommAlgCat.{v} R))

def cohomologyCup (p q : ℕ) :
    (ModuleComplex.complex A).homology p →ₗ[R] (ModuleComplex.complex A).homology q →ₗ[R] (ModuleComplex.complex A).homology (p + q) :=
  ((BilinearQuotient.lift₂ (Module.CochainClasses.boundaries (ModuleComplex.complex A) p) (Module.CochainClasses.boundaries (ModuleComplex.complex A) q)
    (ModuleCocycles.Cup.cycleCupClass A p q)
    (fun x hx y => ModuleCocycles.Cup.cycleCupClass_boundary_left A p q x y hx)
    (fun x y hy => ModuleCocycles.Cup.cycleCupClass_boundary_right A p q x y hy)).comp
      (Module.CochainClasses.quotientIso (ModuleComplex.complex A) p).hom.hom).compl₂ (Module.CochainClasses.quotientIso (ModuleComplex.complex A) q).hom.hom

theorem quotient_classMap (n : ℕ) (x : Module.CochainClasses.cycles (ModuleComplex.complex A) n) :
    (Module.CochainClasses.quotientIso (ModuleComplex.complex A) n).hom (Module.CochainClasses.classMap (ModuleComplex.complex A) n x) =
      (Module.CochainClasses.boundaries (ModuleComplex.complex A) n).mkQ x :=
  ConcreteCategory.congr_hom (Module.CochainClasses.quotientIso (ModuleComplex.complex A) n).inv_hom_id
    ((Module.CochainClasses.boundaries (ModuleComplex.complex A) n).mkQ x)

theorem cup_class (p q : ℕ) (x : Module.CochainClasses.cycles (ModuleComplex.complex A) p) (y : Module.CochainClasses.cycles (ModuleComplex.complex A) q) :
    cohomologyCup A p q (Module.CochainClasses.classMap (ModuleComplex.complex A) p x) (Module.CochainClasses.classMap (ModuleComplex.complex A) q y) =
      Module.CochainClasses.classMap (ModuleComplex.complex A) (p + q) (ModuleCocycles.Cup.cycleCup A p q x y) := by
  change BilinearQuotient.lift₂ (Module.CochainClasses.boundaries (ModuleComplex.complex A) p) (Module.CochainClasses.boundaries (ModuleComplex.complex A) q)
    (ModuleCocycles.Cup.cycleCupClass A p q)
    (fun x hx y => ModuleCocycles.Cup.cycleCupClass_boundary_left A p q x y hx)
    (fun x y hy => ModuleCocycles.Cup.cycleCupClass_boundary_right A p q x y hy)
    ((Module.CochainClasses.quotientIso (ModuleComplex.complex A) p).hom (Module.CochainClasses.classMap (ModuleComplex.complex A) p x))
    ((Module.CochainClasses.quotientIso (ModuleComplex.complex A) q).hom (Module.CochainClasses.classMap (ModuleComplex.complex A) q y)) = _
  rw [quotient_classMap, quotient_classMap, BilinearQuotient.lift₂_mkQ]
  rfl

variable {A} {B : CosimplicialObject (CommAlgCat.{v} R)}

def complexMap (f : A ⟶ B) : ModuleComplex.complex A ⟶ ModuleComplex.complex B :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat R)).map
    (Functor.whiskerRight f
      (forget₂ (CommAlgCat R) (AlgCat R) ⋙ forget₂ (AlgCat R) (ModuleCat R)))

theorem complexMap_f_apply (f : A ⟶ B) (n : ℕ) (x : A.obj ⦋n⦌) :
    (complexMap f).f n x = f.app ⦋n⦌ x := rfl

theorem cycleMap_cup (f : A ⟶ B) (p q : ℕ)
    (x : Module.CochainClasses.cycles (ModuleComplex.complex A) p) (y : Module.CochainClasses.cycles (ModuleComplex.complex A) q) :
    Module.CochainClassNaturality.cycleMap (complexMap f) (p + q) (ModuleCocycles.Cup.cycleCup A p q x y) =
      ModuleCocycles.Cup.cycleCup B p q (Module.CochainClassNaturality.cycleMap (complexMap f) p x) (Module.CochainClassNaturality.cycleMap (complexMap f) q y) := by
  apply Subtype.ext
  exact Cup.cup_natural (ModuleComplex.ringObject A)
    (Functor.whiskerRight f (forget₂ (CommAlgCat R) CommRingCat)) x.1 y.1

theorem cohomologyCup_natural (f : A ⟶ B) (p q : ℕ)
    (x : (ModuleComplex.complex A).homology p) (y : (ModuleComplex.complex A).homology q) :
    HomologicalComplex.homologyMap (complexMap f) (p + q) (cohomologyCup A p q x y) =
      cohomologyCup B p q (HomologicalComplex.homologyMap (complexMap f) p x)
        (HomologicalComplex.homologyMap (complexMap f) q y) := by
  obtain ⟨cx, rfl⟩ := Module.CochainClasses.classMap_surjective (ModuleComplex.complex A) p x
  obtain ⟨cy, rfl⟩ := Module.CochainClasses.classMap_surjective (ModuleComplex.complex A) q y
  simp only [cup_class, ← Module.CochainClassNaturality.naturality_apply, cycleMap_cup]

variable (A)

theorem cup_self_eq_zero [Invertible (2 : A.obj ⦋1⦌)] [Invertible (2 : A.obj ⦋2⦌)]
    (x : (ModuleComplex.complex A).homology 1) : cohomologyCup A 1 1 x x = 0 := by
  obtain ⟨cx, rfl⟩ := Module.CochainClasses.classMap_surjective (ModuleComplex.complex A) 1 x
  rw [cup_class]
  apply (Module.CochainClasses.classMap_succ_eq_zero_iff (ModuleComplex.complex A) 1 (ModuleCocycles.Cup.cycleCup A 1 1 cx cx)).mpr
  let : Invertible (2 : (ModuleComplex.ringObject A).obj ⦋1⦌) := ‹Invertible (2 : A.obj ⦋1⦌)›
  let : Invertible (2 : (ModuleComplex.ringObject A).obj ⦋2⦌) := ‹Invertible (2 : A.obj ⦋2⦌)›
  obtain ⟨z, hz⟩ := OneCupBoundary.cup_self_isBoundary
    (ModuleComplex.ringObject A) cx.1 (ModuleComplex.cycle_differential A cx)
  exact ⟨z, (ModuleComplex.complex_d_apply A 1 z).trans hz⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ModuleCup
