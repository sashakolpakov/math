import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ResolutionSource
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.PositiveNaturality

/-! # Positive Source -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.PositiveSource.AcyclicPositiveSource

noncomputable section

/-! # Source naturality on original positive resolution cohomology -/

open _root_.CategoryTheory

open _root_.CategoryTheory.Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] {X X' : C} (u : X' ⟶ X)
  (K : CochainComplex C ℕ) {Z : C}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]
  (hK : ∀ j q, Subsingleton (Ext.{z} X (K.X j) (q + 1)))
  (hK' : ∀ j q, Subsingleton (Ext.{z} X' (K.X j) (q + 1)))

theorem naturality (n : ℕ) (x : (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K).homology (n + 1)) :
    (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.positiveHomologyIso R X' K ι hK' n).hom
      (HomologicalComplex.homologyMap (ExtSource.ExtSourceSections.complexMap R u K) (n + 1) x) =
    (Ext.mk₀ u).precomp Z (zero_add _)
      ((NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.positiveHomologyIso R X K ι hK n).hom x) := by
  have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (PositiveNaturality.AcyclicPositiveNaturality.adjacent_naturality (ExtSource.ExtSourceSections.complexMap R u K) n)) x
  exact (congrArg (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.shortHomologyIso R X' K ι hK' n).hom h).trans
    (ResolutionSource.AcyclicResolutionSource.short_naturality R u K ι hK hK' n
      (((NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K).homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom x))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.PositiveSource.AcyclicPositiveSource
