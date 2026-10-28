import OAI.AlgebraicGeometry.Comparison.Betti.Module.HomologyClasses
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Cochain Classes -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.CochainClasses.Homology

noncomputable section

/-! Actual cochain classes, using explicit adjacent degrees, and their naturality. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe v u

variable {R : Type u} [Ring R]

def adjacentHomologyIso (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    K.homology n ≅ (K.sc' (n - 1) n (n + 1)).homology :=
  (HomologicalComplex.homologyFunctorIso' (ModuleCat.{v} R) (ComplexShape.up ℕ)
    (n - 1) n (n + 1) (by cases n <;> simp) (CochainComplex.next ℕ n)).app K

def cochainClass (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (x : K.X n) (hx : K.d n (n + 1) x = 0) : K.homology n :=
  (adjacentHomologyIso K n).inv (Module.HomologyClasses.homologyClass (K.sc' (n - 1) n (n + 1)) x hx)

theorem cochainClass_surjective (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (a : K.homology n) : ∃ (x : K.X n) (hx : K.d n (n + 1) x = 0), cochainClass K n x hx = a := by
  obtain ⟨x, hx, hxa⟩ := Module.HomologyClasses.homologyClass_surjective (K.sc' (n - 1) n (n + 1))
    ((adjacentHomologyIso K n).hom a)
  refine ⟨x, hx, ?_⟩
  change (adjacentHomologyIso K n).inv _ = a
  rw [hxa]
  exact (adjacentHomologyIso K n).toLinearEquiv.symm_apply_apply a

theorem cochain_map_closed {K L : CochainComplex (ModuleCat.{v} R) ℕ}
    (f : K ⟶ L) (n : ℕ) (x : K.X n) (hx : K.d n (n + 1) x = 0) :
    L.d n (n + 1) (f.f n x) = 0 := by
  have h := ConcreteCategory.congr_hom (f.comm n (n + 1)) x
  simpa only [ConcreteCategory.comp_apply, hx, map_zero] using h

theorem cochainClass_naturality {K L : CochainComplex (ModuleCat.{v} R) ℕ}
    (f : K ⟶ L) (n : ℕ) (x : K.X n) (hx : K.d n (n + 1) x = 0) :
    HomologicalComplex.homologyMap f n (cochainClass K n x hx) =
      cochainClass L n (f.f n x) (cochain_map_closed f n x hx) := by
  let e := HomologicalComplex.homologyFunctorIso' (ModuleCat.{v} R) (ComplexShape.up ℕ)
    (n - 1) n (n + 1) (by cases n <;> simp) (CochainComplex.next ℕ n)
  let sf := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} R) (ComplexShape.up ℕ)
    (n - 1) n (n + 1)).map f
  have h := ConcreteCategory.congr_hom (e.inv.naturality f)
    (Module.HomologyClasses.homologyClass (K.sc' (n - 1) n (n + 1)) x hx)
  change HomologicalComplex.homologyMap f n ((e.inv.app K) _) = (e.inv.app L) _
  calc
    _ = (e.inv.app L) (ShortComplex.homologyMap sf
        (Module.HomologyClasses.homologyClass (K.sc' (n - 1) n (n + 1)) x hx)) := h.symm
    _ = _ := congrArg (e.inv.app L) (Module.HomologyClasses.homologyClass_naturality sf x hx)

end

end OAI.AlgebraicGeometry.Comparison.Betti.CochainClasses.Homology
