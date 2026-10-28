import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.TransportNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ExtPullbackComparison

/-! # Section Transport Factor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.SectionTransportFactor

noncomputable section

/-! Exact section transport factors through source pullback and the actual target-complex map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Linear R] (X : C) {Y : D} (u : Y ⟶ F.obj X)
  {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
  (f : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L)

def factor : Resolution.Comparison.complex R X K ⟶ Resolution.Comparison.complex R Y L :=
  IntegralComparison.Ext.ExtPullbackComparison.complexMap F R X u K ≫
    ((IntegralComparison.Ext.ModuleFunctor.functor R Y 0).mapHomologicalComplex (.up ℕ)).map f

theorem eq_factor : AlgebraicGeometry.Crystalline.Cohomology.Acyclic.TransportNaturality.AcyclicTransportNaturality.sectionMap R F X u f = factor R F X u f := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ u) (x.mapExactFunctor F) (Ext.mk₀ (f.f i))
    (zero_add 0)).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.SectionTransportFactor
