import OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.ResolutionNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.ComplexHomology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.PositiveNaturality

/-! # Positive Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.PositiveNaturality.SemilinearPositiveNaturality

noncomputable section

/-! # Original positive-degree comparison under exact semilinear transport -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open _root_.CategoryTheory.Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v u' v' z t t'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (R : Type t) (S : Type t') [CommRing R] [CommRing S] [Linear R C] [Linear S D]
  (σ : R →+* S) (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (hF : ∀ (Y : C) (r : R), F.map (r • 𝟙 Y) = σ r • 𝟙 (F.obj Y)) (X : C)
  {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
  (f : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L) {Z : C} {Z' : D}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]
  (κ : (CochainComplex.single₀ D).obj Z' ⟶ L) [QuasiIso κ]
  (a : F.obj Z ⟶ Z') (ha : F.map (ι.f 0) ≫ f.f 0 = a ≫ κ.f 0)
  (hK : ∀ j q, Subsingleton (Ext.{z} X (K.X j) (q + 1)))
  (hL : ∀ j q, Subsingleton (Ext.{z} (F.obj X) (L.X j) (q + 1)))

local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.AcyclicHomologyData.SemilinearAcyclicHomologyData.coefficients R S σ
local notation "KR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K
local notation "LS" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex S (F.obj X) L
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor S (F.obj X) 0
local notation "g" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.ResolutionNaturality.SemilinearResolutionNaturality.sectionMap R S σ F hF X f

include ha in
theorem naturality (n : ℕ) (x : (KR).homology (n + 1)) :
    (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.positiveHomologyIso S (F.obj X) L κ hL n).hom
      ((Mapped.ComplexHomology.MappedComplexHomology.iso Q LS (n + 1)).hom (HomologicalComplex.homologyMap g (n + 1) x)) =
    (Ext.mk₀ a).postcomp (F.obj X) (add_zero _)
      (((NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.positiveHomologyIso R X K ι hK n).hom x).mapExactFunctor F) := by
  let y := HomologicalComplex.homologyMap g (n + 1) x
  let t := (((NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence L n).map H).mapHomologyIso Q).hom
  have h₁ := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (Mapped.ComplexHomology.MappedComplexHomology.adjacent Q LS n)) y
  have h₂ := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (Acyclic.PositiveNaturality.AcyclicPositiveNaturality.adjacent_naturality g n)) x
  have h : ((LS).homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom
      ((Mapped.ComplexHomology.MappedComplexHomology.iso Q LS (n + 1)).hom y) =
      t (ShortComplex.homologyMap (AcyclicHomologyData.SemilinearAcyclicHomologyData.sectionMap R S σ F hF X
        (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence K n) (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.differentialSequence L n) (ExactResolution.ExactResolutionCycleMaps.differentialMap F f n))
        (((KR).homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom x)) :=
    h₁.trans (congrArg t h₂)
  exact (congrArg (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.shortHomologyIso S (F.obj X) L κ hL n).hom h).trans
    (ResolutionNaturality.SemilinearResolutionNaturality.short_naturality R S σ F hF X f ι κ a ha hK hL n
      (((KR).homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom x))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.PositiveNaturality.SemilinearPositiveNaturality
