import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ResolutionExactFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.PositiveNaturality

/-! # Positive Exact Functor -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.PositiveExactFunctor.AcyclicPositiveExactFunctor

noncomputable section

/-! # Exact-functor compatibility of the original positive cohomology-to-Ext map -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open _root_.CategoryTheory.Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Linear R] (X : C)
  {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
  (f : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L) {Z : C} {Z' : D}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]
  (κ : (CochainComplex.single₀ D).obj Z' ⟶ L) [QuasiIso κ]
  (a : F.obj Z ⟶ Z') (ha : F.map (ι.f 0) ≫ f.f 0 = a ≫ κ.f 0)
  (hK : ∀ j q, Subsingleton (Ext.{z} X (K.X j) (q + 1)))
  (hL : ∀ j q, Subsingleton (Ext.{z} (F.obj X) (L.X j) (q + 1)))

include ha in
theorem naturality (n : ℕ) (x : (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K).homology (n + 1)) :
    (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.positiveHomologyIso R (F.obj X) L κ hL n).hom
      (HomologicalComplex.homologyMap (ResolutionExactFunctor.AcyclicResolutionExactFunctor.sectionMap R F X f) (n + 1) x) =
    (Ext.mk₀ a).postcomp (F.obj X) (add_zero _)
      (((NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.positiveHomologyIso R X K ι hK n).hom x).mapExactFunctor F) := by
  have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (PositiveNaturality.AcyclicPositiveNaturality.adjacent_naturality (ResolutionExactFunctor.AcyclicResolutionExactFunctor.sectionMap R F X f) n)) x
  exact (congrArg (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.shortHomologyIso R (F.obj X) L κ hL n).hom h).trans
    (ResolutionExactFunctor.AcyclicResolutionExactFunctor.short_naturality R F X f ι κ a ha hK hL n
      (((NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K).homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom x))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.PositiveExactFunctor.AcyclicPositiveExactFunctor
