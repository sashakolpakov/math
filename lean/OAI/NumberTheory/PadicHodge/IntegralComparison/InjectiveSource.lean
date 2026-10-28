import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.SourcePositive
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.SourceZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveSectionCohomology

/-! # Injective Source -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveSource.Comparison

noncomputable section

/-! Source transport in the actual injective section complex is the original precomposition map on Ext. -/

open _root_.CategoryTheory

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] {X X' : C} (f : X' ⟶ X)
  {Z : C} (I : InjectiveResolution Z)

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (IntegralComparison.Ext.SourceModule.complexMap R f I.cocomplex) i ≫
    (InjectiveSectionCohomology.homologyIso R X' I i).hom =
      (InjectiveSectionCohomology.homologyIso R X I i).hom ≫ IntegralComparison.Ext.SourceModule.component R f i Z := by
  cases i with
  | zero => exact Acyclic.SourceZero.homology R f I.cocomplex I.ι
  | succ n =>
    exact Acyclic.SourcePositive.homology R f I.cocomplex I.ι
      (fun a q => Ext.subsingleton_of_injective X (I.cocomplex.X a) q)
      (fun a q => Ext.subsingleton_of_injective X' (I.cocomplex.X a) q) n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveSource.Comparison
