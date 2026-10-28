import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.AllDegreesNaturality

/-! # Transport Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.TransportNaturality.AcyclicTransportNaturality

noncomputable section

/-! # Original Ext comparison under exact transport and source identification -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open _root_.CategoryTheory.Abelian OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.AllDegreesComparison.AcyclicAllDegreesComparison

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Linear R] (X : C) {Y : D} (u : Y ⟶ F.obj X)
  {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
  (f : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L)

def sourceSectionMap : NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R (F.obj X) L ⟶
    NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R Y L := ExtSource.ExtSourceSections.complexMap R u L

def sectionMap : NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K ⟶
    NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R Y L :=
  ResolutionExactFunctor.AcyclicResolutionExactFunctor.sectionMap R F X f ≫ sourceSectionMap R F X u

theorem component (n : ℕ) (α : Ext.{z} X (K.X n) 0) :
    ((sectionMap R F X u f).f n).hom α =
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
    (AllDegreesComparison.AcyclicAllDegreesComparison.homologyIso R Y L κ hL' n).hom (HomologicalComplex.homologyMap (sectionMap R F X u f) n x) =
      (Ext.mk₀ u).precomp Z' (zero_add n)
        ((Ext.mk₀ a).postcomp (F.obj X) (add_zero n)
          (((AllDegreesComparison.AcyclicAllDegreesComparison.homologyIso R X K ι hK n).hom x).mapExactFunctor F)) := by
  let f₁ := ResolutionExactFunctor.AcyclicResolutionExactFunctor.sectionMap R F X f
  let f₂ := sourceSectionMap R F X u (L := L)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{z} R) (.up ℕ) n
  have hm : HomologicalComplex.homologyMap (sectionMap R F X u f) n x =
      HomologicalComplex.homologyMap f₂ n (HomologicalComplex.homologyMap f₁ n x) :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (H.map_comp f₁ f₂)) x
  have hs := AllDegreesNaturality.AcyclicAllDegreesNaturality.source R u L κ hL hL' n
    (HomologicalComplex.homologyMap f₁ n x)
  have hf := AllDegreesNaturality.AcyclicAllDegreesNaturality.exactFunctor R F X f ι κ a ha hK hL n x
  exact (congrArg (AllDegreesComparison.AcyclicAllDegreesComparison.homologyIso R Y L κ hL' n).hom hm).trans
    (hs.trans (congrArg ((Ext.mk₀ u).precomp Z' (zero_add n)) hf))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.TransportNaturality.AcyclicTransportNaturality
