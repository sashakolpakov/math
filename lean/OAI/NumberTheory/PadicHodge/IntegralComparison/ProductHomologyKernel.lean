import OAI.NumberTheory.PadicHodge.IntegralComparison.CountableProductHomology

/-! # Product Homology Kernel -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProductHomologyKernel

noncomputable section

/-! An injective cohomology map into a countable product is detected by its actual component maps. -/

open _root_.CategoryTheory

universe u

variable (R : Type u) [CommRing R] (K : CochainComplex (Discrete ℕ ⥤ ModuleCat.{u} R) ℕ)
  (P : CochainComplex (ModuleCat.{u} R) ℕ) (f : P ⟶ CountableProductHomology.complex R K)

theorem zero_of_projections (i : ℕ) [Mono (HomologicalComplex.homologyMap f i)]
    (x : P.homology i)
    (hx : ∀ n, HomologicalComplex.homologyMap (f ≫ CountableProductHomology.projection R K n) i x = 0) :
    x = 0 := by
  let e := (CountableProductHomology.homologyIso R K i).toLinearEquiv
  have hy : e (HomologicalComplex.homologyMap f i x) = 0 := by
    funext n
    have hp := congrArg (fun a => a (HomologicalComplex.homologyMap f i x))
      (CountableProductHomology.homologyIso_projection R K i n)
    have hm := congrArg (fun a => a x)
      (HomologicalComplex.homologyMap_comp f (CountableProductHomology.projection R K n) i)
    exact hp.trans (hm.symm.trans (hx n))
  have hz : HomologicalComplex.homologyMap f i x = 0 := e.injective (hy.trans e.map_zero.symm)
  exact ((ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap f i)).mp inferInstance)
    (hz.trans (HomologicalComplex.homologyMap f i).hom.map_zero.symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProductHomologyKernel
