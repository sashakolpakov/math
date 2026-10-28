import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Semilinear Complex Map -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap

noncomputable section

/-! # Semilinear maps of actual module complexes and their categorical cohomology -/

open _root_.CategoryTheory

universe u
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
  (C : CochainComplex (ModuleCat.{u} R) ℕ) (D : CochainComplex (ModuleCat.{u} S) ℕ)

structure Map where
  f : ∀ n, C.X n →ₛₗ[φ] D.X n
  comm : ∀ i j x, f j ((C.d i j).hom x) = (D.d i j).hom (f i x)

variable {φ C D}

def ofSuccessors (f : ∀ n, C.X n →ₛₗ[φ] D.X n)
    (hf : ∀ n x, f (n + 1) ((C.d n (n + 1)).hom x) = (D.d n (n + 1)).hom (f n x)) : Map φ C D where
  f := f
  comm i j x := by
    by_cases hij : i + 1 = j
    · subst j
      exact hf i x
    · have hrel : ¬ (ComplexShape.up ℕ).Rel i j := hij
      rw [C.shape i j hrel, D.shape i j hrel]
      exact map_zero (f j)

variable (f : Map φ C D)

def cycleMap (n : ℕ) : LinearMap.ker (C.sc n).g.hom →ₛₗ[φ] LinearMap.ker (D.sc n).g.hom :=
  ((f.f n).comp (LinearMap.ker (C.sc n).g.hom).subtype).codRestrict _ (fun x => by
    have h := f.comm n ((ComplexShape.up ℕ).next n) x.val
    have hx : (C.sc n).g.hom x.val = 0 := x.property
    exact h.symm.trans ((congrArg (f.f ((ComplexShape.up ℕ).next n)) hx).trans (map_zero _)))

theorem cycleMap_boundaries (n : ℕ) :
    LinearMap.range (C.sc n).moduleCatToCycles ≤
      (LinearMap.range (D.sc n).moduleCatToCycles).comap (cycleMap f n) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨f.f ((ComplexShape.up ℕ).prev n) x, ?_⟩
  apply Subtype.ext
  exact (f.comm ((ComplexShape.up ℕ).prev n) n x).symm

def quotientMap (n : ℕ) :
    (LinearMap.ker (C.sc n).g.hom ⧸ LinearMap.range (C.sc n).moduleCatToCycles) →ₛₗ[φ]
      (LinearMap.ker (D.sc n).g.hom ⧸ LinearMap.range (D.sc n).moduleCatToCycles) :=
  (LinearMap.range (C.sc n).moduleCatToCycles).mapQ (LinearMap.range (D.sc n).moduleCatToCycles)
    (cycleMap f n) (cycleMap_boundaries f n)

def homologyMap (n : ℕ) : C.homology n →ₛₗ[φ] D.homology n :=
  (D.sc n).moduleCatHomologyIso.inv.hom.comp
    ((quotientMap f n).comp (C.sc n).moduleCatHomologyIso.hom.hom)

theorem homologyMap_quotient (n : ℕ) (x : C.homology n) :
    (D.sc n).moduleCatHomologyIso.hom (homologyMap f n x) =
      quotientMap f n ((C.sc n).moduleCatHomologyIso.hom x) := by
  exact congrArg (fun g => g.hom (quotientMap f n ((C.sc n).moduleCatHomologyIso.hom x)))
    (D.sc n).moduleCatHomologyIso.inv_hom_id

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap
