import OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.ZeroNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.PositiveNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.AllDegreesComparison

/-! # All Degrees Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.AllDegreesNaturality.SemilinearAllDegreesNaturality

noncomputable section

/-! # Exact semilinear naturality of the original Ext comparison in every degree -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open _root_.CategoryTheory.Abelian OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.AllDegreesComparison.AcyclicAllDegreesComparison

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

include ha in
theorem naturality (n : ℕ) (x : (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K).homology n) :
    (Acyclic.AllDegreesComparison.AcyclicAllDegreesComparison.homologyIso S (F.obj X) L κ hL n).hom
      ((Mapped.ComplexHomology.MappedComplexHomology.iso (AcyclicHomologyData.SemilinearAcyclicHomologyData.coefficients R S σ)
        (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex S (F.obj X) L) n).hom
        (HomologicalComplex.homologyMap (ResolutionNaturality.SemilinearResolutionNaturality.sectionMap R S σ F hF X f) n x)) =
    (Ext.mk₀ a).postcomp (F.obj X) (add_zero n)
      (((Acyclic.AllDegreesComparison.AcyclicAllDegreesComparison.homologyIso R X K ι hK n).hom x).mapExactFunctor F) := by
  cases n with
  | zero =>
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      (ZeroNaturality.SemilinearZeroNaturality.naturality R S σ F hF X f ι κ a ha)) x
  | succ n => exact PositiveNaturality.SemilinearPositiveNaturality.naturality R S σ F hF X f ι κ a ha hK hL n x

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.AllDegreesNaturality.SemilinearAllDegreesNaturality
