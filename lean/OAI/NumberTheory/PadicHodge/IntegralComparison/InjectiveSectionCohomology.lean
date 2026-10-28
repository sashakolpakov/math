import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-! # Injective Section Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveSectionCohomology

noncomputable section

/-!
# IntegralComparison: original Ext is computed by the coefficient-linear injective section complex
-/

open _root_.CategoryTheory

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (X : C) {Z : C} (I : InjectiveResolution Z)

abbrev complex : CochainComplex (ModuleCat.{z} R) ℕ :=
  Acyclic.Resolution.Comparison.complex R X I.cocomplex

def homologyIso (i : ℕ) : (complex R X I).homology i ≅ ModuleCat.of R (Abelian.Ext.{z} X Z i) := by
  cases i with
  | zero => exact Acyclic.ResolutionZero.Comparison.homologyIso R X I.cocomplex I.ι
  | succ i =>
    exact Acyclic.Resolution.Comparison.positiveHomologyIso R X I.cocomplex I.ι
      (fun n q => Abelian.Ext.subsingleton_of_injective X (I.cocomplex.X n) q) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveSectionCohomology
