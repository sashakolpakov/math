import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.TransportNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius

/-! # Iso Transport Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.IsoTransportNaturality

noncomputable section

/-! Acyclic resolution comparison commutes with exact Ext transport through source and target isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Linear R] (X : C) {Y : D} (e : F.obj X ≅ Y)
  {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
  (f : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L)
  {Z : C} {Z' : D}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]
  (κ : (CochainComplex.single₀ D).obj Z' ⟶ L) [QuasiIso κ]
  (s : F.obj Z ≅ Z') (hs : F.map (ι.f 0) ≫ f.f 0 = s.hom ≫ κ.f 0)
  (hK : ∀ j q, Subsingleton (Ext.{z} X (K.X j) (q + 1)))
  (hL : ∀ j q, Subsingleton (Ext.{z} (F.obj X) (L.X j) (q + 1)))
  (hL' : ∀ j q, Subsingleton (Ext.{z} Y (L.X j) (q + 1)))

include hs hK hL hL' in
theorem naturality (i : ℕ) (x : (Resolution.Comparison.complex R X K).homology i) :
    (AlgebraicGeometry.Crystalline.Cohomology.Acyclic.AllDegreesComparison.AcyclicAllDegreesComparison.homologyIso R Y L κ hL' i).hom
      (HomologicalComplex.homologyMap (AlgebraicGeometry.Crystalline.Cohomology.Acyclic.TransportNaturality.AcyclicTransportNaturality.sectionMap R F X e.inv f) i x) =
    Etale.Frobenius.extIsoCongr R e s i
      (((AlgebraicGeometry.Crystalline.Cohomology.Acyclic.AllDegreesComparison.AcyclicAllDegreesComparison.homologyIso R X K ι hK i).hom x).mapExactFunctor F) := by
  have h := AlgebraicGeometry.Crystalline.Cohomology.Acyclic.TransportNaturality.AcyclicTransportNaturality.naturality R F X e.inv f ι κ s.hom hs hK hL hL' i x
  exact h.trans (Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add i)).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.IsoTransportNaturality
