import OAI.NumberTheory.PadicHodge.IntegralComparison.CountableCohomologyDifference
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.InverseDifference

/-! # Product Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.ProductCohomology

noncomputable section

/-!
# IntegralComparison: finite component cohomology makes the cohomological difference surjective
-/

open _root_.CategoryTheory

universe u

variable (R : Type u) [CommRing R] (K : CochainComplex (Discrete ℕ ⥤ ModuleCat.{u} R) ℕ)
  (φ : CountableProductHomology.complex R K ⟶ CountableProductHomology.complex R K)
  (t : ∀ n, CountableProductHomology.component R K (n + 1) ⟶ CountableProductHomology.component R K n)
  (hφ : ∀ n, φ ≫ CountableProductHomology.projection R K n =
    CountableProductHomology.projection R K n - CountableProductHomology.projection R K (n + 1) ≫ t n)

include hφ in
theorem surjective (i : ℕ) [∀ n, Finite ((CountableProductHomology.component R K n).homology i)] :
    Function.Surjective (HomologicalComplex.homologyMap φ i) := by
  let e := (CountableProductHomology.homologyIso R K i).toLinearEquiv
  intro y
  obtain ⟨x, hx⟩ := InverseDifference.surjective R
    (fun n => (CountableProductHomology.component R K n).homology i)
    (fun n => (HomologicalComplex.homologyMap (t n) i).hom) (e y)
  refine ⟨e.symm x, e.injective ?_⟩
  apply funext
  intro n
  exact (CountableCohomologyDifference.difference_apply R K φ t hφ i x n).trans
    (congrFun hx n)

include hφ in
theorem epi (i : ℕ) [∀ n, Finite ((CountableProductHomology.component R K n).homology i)] :
    Epi (HomologicalComplex.homologyMap φ i) :=
  (ModuleCat.epi_iff_surjective _).mpr (surjective R K φ t hφ i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.ProductCohomology
