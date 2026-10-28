import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.AllDegreesComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.PositiveSource
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ZeroSource
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.PositiveExactFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ZeroExactFunctor

/-! # All Degrees Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.AllDegreesNaturality.AcyclicAllDegreesNaturality

noncomputable section

/-! # Source and exact-functor naturality in every original cohomological degree -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open _root_.CategoryTheory.Abelian OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.AllDegreesComparison.AcyclicAllDegreesComparison

universe u v u' v' z t

section Source

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] {X X' : C} (u : X' ⟶ X)
  (K : CochainComplex C ℕ) {Z : C}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]
  (hK : ∀ j q, Subsingleton (Ext.{z} X (K.X j) (q + 1)))
  (hK' : ∀ j q, Subsingleton (Ext.{z} X' (K.X j) (q + 1)))

theorem source (n : ℕ) (x : (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K).homology n) :
    (AllDegreesComparison.AcyclicAllDegreesComparison.homologyIso R X' K ι hK' n).hom
      (HomologicalComplex.homologyMap (ExtSource.ExtSourceSections.complexMap R u K) n x) =
      (Ext.mk₀ u).precomp Z (zero_add n) ((AllDegreesComparison.AcyclicAllDegreesComparison.homologyIso R X K ι hK n).hom x) := by
  cases n with
  | zero =>
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (ZeroSource.AcyclicZeroSource.naturality R u K ι)) x
  | succ n => exact PositiveSource.AcyclicPositiveSource.naturality R u K ι hK hK' n x

end Source

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Linear R] (X : C) {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
  (f : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L) {Z : C} {Z' : D}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]
  (κ : (CochainComplex.single₀ D).obj Z' ⟶ L) [QuasiIso κ]
  (a : F.obj Z ⟶ Z') (ha : F.map (ι.f 0) ≫ f.f 0 = a ≫ κ.f 0)
  (hK : ∀ j q, Subsingleton (Ext.{z} X (K.X j) (q + 1)))
  (hL : ∀ j q, Subsingleton (Ext.{z} (F.obj X) (L.X j) (q + 1)))

include ha in
theorem exactFunctor (n : ℕ) (x : (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K).homology n) :
    (AllDegreesComparison.AcyclicAllDegreesComparison.homologyIso R (F.obj X) L κ hL n).hom
      (HomologicalComplex.homologyMap (ResolutionExactFunctor.AcyclicResolutionExactFunctor.sectionMap R F X f) n x) =
      (Ext.mk₀ a).postcomp (F.obj X) (add_zero n) (((AllDegreesComparison.AcyclicAllDegreesComparison.homologyIso R X K ι hK n).hom x).mapExactFunctor F) := by
  cases n with
  | zero =>
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (ZeroExactFunctor.AcyclicZeroExactFunctor.naturality R F X f ι κ a ha)) x
  | succ n => exact PositiveExactFunctor.AcyclicPositiveExactFunctor.naturality R F X f ι κ a ha hK hL n x

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.AllDegreesNaturality.AcyclicAllDegreesNaturality
