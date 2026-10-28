import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyVanishingDescent
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Equivalence Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.EquivalenceCohomology

noncomputable section

/-! A single monomorphism into an autoequivalence produces an actual sequence of injections. Its successive cokernels are the corresponding iterates of the original cokernel, so cohomology vanishing descends through that exact sequence. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u v

def iterateAutoEquivalence {C : Type u} [Category.{v} C] (E : C ≌ C) : ℕ → (C ≌ C)
  | 0 => CategoryTheory.Equivalence.refl
  | n + 1 => E.trans (iterateAutoEquivalence E n)

def iterateAutoEquivalenceMap {C : Type u} [Category.{v} C] (E : C ≌ C)
    {M : C} (s : M ⟶ E.functor.obj M) (n : ℕ) :
    (EquivalenceCohomology.iterateAutoEquivalence E n).functor.obj M ⟶
      (EquivalenceCohomology.iterateAutoEquivalence E (n + 1)).functor.obj M :=
  (EquivalenceCohomology.iterateAutoEquivalence E n).functor.map s

theorem iterateAutoEquivalenceMap_mono {C : Type u} [Category.{v} C]
    (E : C ≌ C) {M : C} (s : M ⟶ E.functor.obj M) [Mono s] (n : ℕ) :
    Mono (iterateAutoEquivalenceMap E s n) := by
  change Mono ((EquivalenceCohomology.iterateAutoEquivalence E n).functor.map s)
  infer_instance

def iterateAutoEquivalenceCokernelIso {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
    (E : C ≌ C) {M : C} (s : M ⟶ E.functor.obj M) [HasCokernel s]
    (n : ℕ) [HasCokernel (iterateAutoEquivalenceMap E s n)] :
    (EquivalenceCohomology.iterateAutoEquivalence E n).functor.obj (cokernel s) ≅
      cokernel (iterateAutoEquivalenceMap E s n) :=
  PreservesCokernel.iso (EquivalenceCohomology.iterateAutoEquivalence E n).functor s

namespace ZariskiCohomology

theorem coefficientCohomology_vanish_of_iterated_cokernel
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤))
    (E : X.Modules ≌ X.Modules) {M : X.Modules} (s : M ⟶ E.functor.obj M) [Mono s] (q : ℕ)
    (hQ : ∀ m, IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).obj
      ((EquivalenceCohomology.iterateAutoEquivalence E m).functor.obj (cokernel s))))
    (hM : ∃ B, ∀ m, B ≤ m → IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (q + 1)).obj
      ((EquivalenceCohomology.iterateAutoEquivalence E m).functor.obj M))) :
    IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (q + 1)).obj M) := by
  let T : ℕ → X.Modules := fun m => (EquivalenceCohomology.iterateAutoEquivalence E m).functor.obj M
  let f : ∀ m, T m ⟶ T (m + 1) := iterateAutoEquivalenceMap E s
  have hmono (m : ℕ) : Mono (f m) := iterateAutoEquivalenceMap_mono E s m
  have hcoker (m : ℕ) : IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).obj (cokernel (f m))) := by
    exact ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c q).mapIso
      (iterateAutoEquivalenceCokernelIso E s m)).isZero_iff.mp (hQ m)
  exact CohomologyVanishingDescent.ZariskiCohomology.coefficientCohomology_vanish_of_eventual_twists c T f hmono q hcoker hM 0

end ZariskiCohomology

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.EquivalenceCohomology
