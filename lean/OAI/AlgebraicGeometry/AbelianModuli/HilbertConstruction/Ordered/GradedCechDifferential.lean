import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.SubsetSigns
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Card

/-! # Graded Cech Differential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.GradedCechDifferential

noncomputable section

/-! The graded finite-subset Čech differential is the ordered alternating sum over tuple positions. -/

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Card.ProjectiveCech

universe u v w

variable {σ : Type u} [LinearOrder σ] (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
    [IsScalarTower R (MvPolynomial σ R) M]

theorem moduleCechDifferential_ordered {q : ℕ} (a : SectionCechIndices.OrderedCechIndex σ q)
    (f : HilbertScheme.Presentations.ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) :
    HilbertScheme.Presentations.ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f (OrderedCech.FiniteSubsets.orderedCechIndexFinset a) =
      ∑ k : Fin (q + 1), (-1 : R) ^ k.val •
        HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.erase_subset (a.val k) (OrderedCech.FiniteSubsets.orderedCechIndexFinset a))
          (f ((OrderedCech.FiniteSubsets.orderedCechIndexFinset a).erase (a.val k))) := by
  let S := OrderedCech.FiniteSubsets.orderedCechIndexFinset a
  let t := fun i : σ ↦ HilbertScheme.Presentations.Cech.Signs.ProjectiveCech.alternatingSign R S i •
    HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.erase_subset i S) (f (S.erase i))
  have hs : (∑ i ∈ S, t i) = ∑ k : Fin (q + 1), t (a.val k) :=
    Finset.sum_image (fun _ _ _ _ h ↦ a.property.injective h)
  apply hs.trans
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun r : R ↦ r •
    HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.erase_subset (a.val k) S) (f (S.erase (a.val k))))
      (OrderedCech.SubsetSigns.orderedCechIndexFinset_sign R a k)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.GradedCechDifferential
