import OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.AllDegreesNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.AllDegreesNaturality

/-! # Transport Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.TransportNaturality.SemilinearTransportNaturality

noncomputable section

/-! # Original Ext comparison under semilinear transport and source identification -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open _root_.CategoryTheory.Abelian OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.AllDegreesComparison.AcyclicAllDegreesComparison

universe u v u' v' z t t'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (R : Type t) (S : Type t') [CommRing R] [CommRing S] [Linear R C] [Linear S D]
  (σ : R →+* S) (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (hF : ∀ (Y : C) (r : R), F.map (r • 𝟙 Y) = σ r • 𝟙 (F.obj Y))
  (X : C) {Y : D} (u : Y ⟶ F.obj X)
  {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
  (f : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L)

local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.AcyclicHomologyData.SemilinearAcyclicHomologyData.coefficients R S σ

def sourceMap : NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex S (F.obj X) L ⟶
    NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex S Y L := ExtSource.ExtSourceSections.complexMap S u L

def sectionMap : NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K ⟶
    ((Q).mapHomologicalComplex (.up ℕ)).obj (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex S Y L) :=
  ResolutionNaturality.SemilinearResolutionNaturality.sectionMap R S σ F hF X f ≫
    ((Q).mapHomologicalComplex (.up ℕ)).map (sourceMap S F X u)

theorem component (n : ℕ) (α : Ext.{z} X (K.X n) 0) :
    ((sectionMap R S σ F hF X u f).f n).hom α =
      (Ext.mk₀ u).comp ((α.mapExactFunctor F).comp (Ext.mk₀ (f.f n)) (add_zero 0)) (zero_add 0) := rfl

variable {Z : C} {Z' : D}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]
  (κ : (CochainComplex.single₀ D).obj Z' ⟶ L) [QuasiIso κ]
  (a : F.obj Z ⟶ Z') (ha : F.map (ι.f 0) ≫ f.f 0 = a ≫ κ.f 0)
  (hK : ∀ j q, Subsingleton (Ext.{z} X (K.X j) (q + 1)))
  (hL : ∀ j q, Subsingleton (Ext.{z} (F.obj X) (L.X j) (q + 1)))
  (hL' : ∀ j q, Subsingleton (Ext.{z} Y (L.X j) (q + 1)))

include ha hL in
theorem naturality (n : ℕ) (x : (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K).homology n) :
    (Acyclic.AllDegreesComparison.AcyclicAllDegreesComparison.homologyIso S Y L κ hL' n).hom
      ((Mapped.ComplexHomology.MappedComplexHomology.iso Q (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex S Y L) n).hom
        (HomologicalComplex.homologyMap (sectionMap R S σ F hF X u f) n x)) =
    (Ext.mk₀ u).precomp Z' (zero_add n)
      ((Ext.mk₀ a).postcomp (F.obj X) (add_zero n)
        (((Acyclic.AllDegreesComparison.AcyclicAllDegreesComparison.homologyIso R X K ι hK n).hom x).mapExactFunctor F)) := by
  let f₁ := ResolutionNaturality.SemilinearResolutionNaturality.sectionMap R S σ F hF X f
  let s := sourceMap S F X u (L := L)
  let f₂ := ((Q).mapHomologicalComplex (.up ℕ)).map s
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{z} R) (.up ℕ) n
  let y := HomologicalComplex.homologyMap f₁ n x
  let tX := (Mapped.ComplexHomology.MappedComplexHomology.iso Q (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex S (F.obj X) L) n).hom
  let tY := (Mapped.ComplexHomology.MappedComplexHomology.iso Q (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex S Y L) n).hom
  have hc : HomologicalComplex.homologyMap (sectionMap R S σ F hF X u f) n x =
      HomologicalComplex.homologyMap f₂ n y :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (H.map_comp f₁ f₂)) x
  have ht : tY (HomologicalComplex.homologyMap f₂ n y) = HomologicalComplex.homologyMap s n (tX y) :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (Mapped.ComplexHomologyNaturality.MappedComplexHomologyNaturality.naturality Q s n)) y
  have hs := Acyclic.AllDegreesNaturality.AcyclicAllDegreesNaturality.source S u L κ hL hL' n (tX y)
  have hf := AllDegreesNaturality.SemilinearAllDegreesNaturality.naturality R S σ F hF X f ι κ a ha hK hL n x
  exact (congrArg (Acyclic.AllDegreesComparison.AcyclicAllDegreesComparison.homologyIso S Y L κ hL' n).hom ((congrArg tY hc).trans ht)).trans
    (hs.trans (congrArg ((Ext.mk₀ u).precomp Z' (zero_add n)) hf))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.TransportNaturality.SemilinearTransportNaturality
