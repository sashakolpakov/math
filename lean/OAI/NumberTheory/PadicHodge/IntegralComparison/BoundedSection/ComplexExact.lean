import OAI.NumberTheory.PadicHodge.IntegralComparison.AllBoundedSectionsFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Complex Exact -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.ComplexExact

noncomputable section

/-!
# IntegralComparison: the inverse-limit short exact sequence of section complexes
-/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustivePresheafSections

universe u v w z t

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
  [Preadditive D] (R : Type t) [CommRing R] [Linear R D]
  (P : ℕ → ObjectProperty C) (hP : Monotone P) (M : D)
  (K : CochainComplex (Cᵒᵖ ⥤ D) ℕ)

def compatibleComplex : CochainComplex (ModuleCat.{max u z} R) ℕ :=
  ((ExhaustiveSectionNaturality.boundedSectionsFunctor R P hP M).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

def allComplex : CochainComplex (ModuleCat.{max u z} R) ℕ :=
  ((AllBoundedSectionsFunctor.functor R P M).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

def inclusion : compatibleComplex R P hP M K ⟶ allComplex R P M K :=
  (NatTrans.mapHomologicalComplex (AllBoundedSectionsFunctor.inclusion R P hP M) (ComplexShape.up ℕ)).app K

def difference : allComplex R P M K ⟶ allComplex R P M K :=
  (NatTrans.mapHomologicalComplex (AllBoundedSectionsFunctor.difference R P hP M) (ComplexShape.up ℕ)).app K

def sequence : ShortComplex (CochainComplex (ModuleCat.{max u z} R) ℕ) :=
  ShortComplex.mk (inclusion R P hP M K) (difference R P hP M K) (by
    apply HomologicalComplex.Hom.ext
    funext i
    exact NatTrans.congr_app (AllBoundedSectionsFunctor.inclusion_difference R P hP M) (K.X i))

theorem shortExact
    (ht : ∀ i n, Function.Surjective (ExhaustivePresheafSections.restrict P hP M (K.X i) n (n + 1) (Nat.le_succ n))) :
    (sequence R P hP M K).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun i => BoundedSection.ShortExact.shortExact R P hP M (K.X i) (ht i))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.ComplexExact
