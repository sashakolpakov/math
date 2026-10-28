import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ResolutionNaturality

/-! # Positive Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.PositiveNaturality.AcyclicPositiveNaturality

noncomputable section

/-! # Positive-degree resolution cohomology maps to the original Ext functor naturally -/

open _root_.CategoryTheory

open _root_.CategoryTheory.Abelian

universe u v z t

section Adjacent

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L : CochainComplex C ℕ} (f : K ⟶ L)

theorem adjacent_naturality (n : ℕ) :
    HomologicalComplex.homologyMap f (n + 1) ≫
      (L.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom =
    (K.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom ≫
      ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor' C (.up ℕ) n (n + 1) (n + 2)).map f) := by
  have h := (HomologicalComplex.natIsoSc' C (.up ℕ) n (n + 1) (n + 2) (by simp) (by simp)).hom.naturality f
  have hh := congrArg (ShortComplex.homologyFunctor C).map h
  rw [Functor.map_comp, Functor.map_comp] at hh
  exact hh

end Adjacent

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (X : C)
  {K L : CochainComplex C ℕ} (f : K ⟶ L) {Z Z' : C}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]
  (κ : (CochainComplex.single₀ C).obj Z' ⟶ L) [QuasiIso κ]
  (a : Z ⟶ Z') (ha : ι ≫ f = (CochainComplex.single₀ C).map a ≫ κ)
  (hK : ∀ j q, Subsingleton (Ext.{z} X (K.X j) (q + 1)))
  (hL : ∀ j q, Subsingleton (Ext.{z} X (L.X j) (q + 1)))

include ha in
theorem naturality (n : ℕ) (x : (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K).homology (n + 1)) :
    (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.positiveHomologyIso R X L κ hL n).hom
      (HomologicalComplex.homologyMap (ResolutionNaturality.AcyclicResolutionNaturality.sectionMap R X f) (n + 1) x) =
    (Ext.mk₀ a).postcomp X (add_zero _)
      ((NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.positiveHomologyIso R X K ι hK n).hom x) := by
  have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (adjacent_naturality (ResolutionNaturality.AcyclicResolutionNaturality.sectionMap R X f) n)) x
  exact (congrArg (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.shortHomologyIso R X L κ hL n).hom h).trans
    (ResolutionNaturality.AcyclicResolutionNaturality.short_naturality R X f ι κ a ha hK hL n
      (((NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K).homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom x))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.PositiveNaturality.AcyclicPositiveNaturality
