import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalFlasqueComparison
import OAI.AlgebraicTopology.Cohomology.Singular.SheafSections
import OAI.AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition

/-! # Flasque Section Comparison -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.FlasqueSectionComparison

noncomputable section

/-!
# The flasque edge isomorphism is the actual section comparison

The low-degree flasque isomorphism takes a global cohomology class to its
canonical section of the cohomology sheaf. Identifying these maps ensures
that lifting a sheaf section through the edge isomorphism preserves its
actual restrictions and germs.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

variable {X : TopCat.{0}}

local instance rationalSheafForget_additive_for_sectionComparison :
    (TopCat.Sheaf.forget (ModuleCat.{0} ℚ) X).Additive where
  map_add := rfl

/-- Evaluating the underlying-presheaf comparison is exactly the canonical
left-exact comparison for sections on the specified open set. -/
theorem sheafCohomologySectionMap_eq_leftExactHomologyComparison
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
    (U : Opens X) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.SheafSections.sheafCohomologySectionMap K U n =
      AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactHomologyComparison (K.sc n) (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafSections U) := by
  change (((K.sc n).map (TopCat.Sheaf.forget (ModuleCat.{0} ℚ) X)).mapHomologyIso
      (AlgebraicTopology.Cohomology.Singular.Stalk.presheafSectionFunctor (R := ℚ) U)).hom ≫
        (AlgebraicTopology.Cohomology.Singular.Stalk.presheafSectionFunctor (R := ℚ) U).map
          (AlgebraicTopology.Cohomology.Singular.LeftExactHomology.leftExactHomologyComparison (K.sc n)
            (TopCat.Sheaf.forget (ModuleCat.{0} ℚ) X)) = _
  rw [← AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition.leftExactHomologyComparison_eq_mapHomologyIso,
    AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition.leftExactHomologyComparison_comp]
  rfl

/-- In the low-degree range where the flasque edge map is an isomorphism,
its forward map is the actual cohomology-sheaf section map. -/
theorem rationalFlasqueLowDegreeHomologyIso_hom_eq_sectionMap
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
    (hK : ∀ j, TopCat.Sheaf.IsFlasque (K.X j))
    (d : ℕ) (he : ∀ j, j < d → K.ExactAt j) (n : ℕ) (hn : n ≤ d) :
    (AlgebraicTopology.DeRham.Comparison.RationalFlasqueLowDegree.rationalFlasqueLowDegreeHomologyIso K hK d he n hn).hom =
      AlgebraicTopology.Cohomology.Singular.SheafSections.sheafCohomologySectionMap K ⊤ n := by
  rw [RationalFlasqueComparison.Cycles.rationalFlasqueLowDegreeHomologyIso_hom_eq_leftExactHomologyComparison,
    sheafCohomologySectionMap_eq_leftExactHomologyComparison]

/-- The first potentially nonzero flasque cohomology group is identified
with sections using precisely the canonical section comparison. -/
theorem rationalFlasqueFirstCohomologyIso_hom_eq_sectionMap
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
    (hK : ∀ j, TopCat.Sheaf.IsFlasque (K.X j))
    (d : ℕ) (he : ∀ j, j < d → K.ExactAt j) :
    (AlgebraicTopology.DeRham.Comparison.RationalFlasqueLowDegree.rationalFlasqueFirstCohomologyIso K hK d he).hom =
      AlgebraicTopology.Cohomology.Singular.SheafSections.sheafCohomologySectionMap K ⊤ d :=
  rationalFlasqueLowDegreeHomologyIso_hom_eq_sectionMap K hK d he d le_rfl

/-- A sheaf section lifted through the first-degree flasque isomorphism
returns to that same section under the actual comparison map. -/
@[reassoc (attr := simp)]
theorem rationalFlasqueFirstCohomologyIso_inv_comp_sectionMap
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
    (hK : ∀ j, TopCat.Sheaf.IsFlasque (K.X j))
    (d : ℕ) (he : ∀ j, j < d → K.ExactAt j) :
    (AlgebraicTopology.DeRham.Comparison.RationalFlasqueLowDegree.rationalFlasqueFirstCohomologyIso K hK d he).inv ≫
        AlgebraicTopology.Cohomology.Singular.SheafSections.sheafCohomologySectionMap K ⊤ d = 𝟙 _ := by
  rw [← rationalFlasqueFirstCohomologyIso_hom_eq_sectionMap K hK d he]
  exact (AlgebraicTopology.DeRham.Comparison.RationalFlasqueLowDegree.rationalFlasqueFirstCohomologyIso K hK d he).inv_hom_id

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.FlasqueSectionComparison
