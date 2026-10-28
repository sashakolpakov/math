import OAI.AlgebraicTopology.Cohomology.Singular.SheafSectionStalk
import OAI.AlgebraicTopology.Cohomology.Singular.LeftExactHomologyComposition

/-! # Sheaf Section Germ -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SheafSectionGerm

noncomputable section

/-!
# Actual section-to-cohomology-sheaf maps and germs

Taking the germ of the canonical local cohomology section is the same map
as taking cohomology of the actual cochain germ. The proof compares the
canonical left-exact homology maps with the exact stalk functor, rather
than assuming that an open-section functor preserves homology.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits

variable {R : Type} [Ring R] {X : TopCat.{0}}

local instance sectionGermForget_additive :
    (TopCat.Sheaf.forget (ModuleCat.{0} R) X).Additive where
  map_add := rfl

variable (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ)

/-- Forgetting to presheaves and then taking the actual stalk agrees with
taking homology directly through the exact sheaf-stalk functor. -/
theorem sheafHomologyPresheafComparison_stalk (x : X) (n : ℕ) :
    (Stalk.stalkCohomologyIso (SheafSections.sheafUnderlyingCochainComplex K) x n).hom ≫
        (stalkFunctor (ModuleCat.{0} R) x).map (SheafSections.sheafHomologyPresheafComparison K n) =
      (SheafQuasiIso.sheafStalkCohomologyIso K x n).hom :=
  LeftExactHomologyComposition.mapHomologyIso_comp_leftExact (K.sc n) (TopCat.Sheaf.forget (ModuleCat.{0} R) X)
    (stalkFunctor (ModuleCat.{0} R) x)

/-- The canonical map from local section cohomology to the cohomology
sheaf gives precisely the standard stalk-homology comparison. -/
theorem sheafCohomologySectionComparison_stalk (x : X) (n : ℕ) :
    (SheafSectionStalk.sheafSectionStalkCohomologyIso K x n).hom ≫
        (stalkFunctor (ModuleCat.{0} R) x).map (SheafSections.sheafCohomologySectionComparison K n) =
      (SheafQuasiIso.sheafStalkCohomologyIso K x n).hom := by
  change ((Stalk.stalkCohomologyIso (SheafSections.sheafUnderlyingCochainComplex K) x n).hom ≫
      (stalkFunctor (ModuleCat.{0} R) x).map
        (Stalk.openCohomologyPresheafIso (SheafSections.sheafUnderlyingCochainComplex K) n).inv) ≫
    (stalkFunctor (ModuleCat.{0} R) x).map
      ((Stalk.openCohomologyPresheafIso (SheafSections.sheafUnderlyingCochainComplex K) n).hom ≫
        SheafSections.sheafHomologyPresheafComparison K n) = _
  rw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_assoc]
  exact sheafHomologyPresheafComparison_stalk K x n

/-- Taking the germ of the actual cohomology-sheaf section is cohomology
of the actual cochain germ, followed by the canonical stalk isomorphism. -/
@[reassoc]
theorem sheafCohomologySectionMap_germ
    (U : Opens X) (x : X) (hx : x ∈ U) (n : ℕ) :
    SheafSections.sheafCohomologySectionMap K U n ≫
        TopCat.Presheaf.germ (X := X) (K.homology n).obj U x hx =
      HomologicalComplex.homologyMap (SheafSectionStalk.sheafSectionCochainGerm K U x hx) n ≫
        (SheafQuasiIso.sheafStalkCohomologyIso K x n).hom := by
  change (SheafSections.sheafCohomologySectionComparison K n).app (op U) ≫
    TopCat.Presheaf.germ (X := X) (K.homology n).obj U x hx = _
  rw [← stalkFunctor_map_germ, ← SheafSectionStalk.sheafSectionStalkCohomologyIso_germ,
    Category.assoc, sheafCohomologySectionComparison_stalk]

end

end OAI.AlgebraicTopology.Cohomology.Singular.SheafSectionGerm
