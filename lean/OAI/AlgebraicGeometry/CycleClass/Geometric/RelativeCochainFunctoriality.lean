import OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport

/-! # Relative Cochain Functoriality -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainFunctoriality.Cohomology

noncomputable section

/-! # Expanding relative singular-cochain pullbacks of composite maps

Canonical identity and composition declarations come from `RelativePresheaf`.
The two lemmas here only supply the opposite rewriting orientation.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [Ring R]

theorem relativeSingularCochainsMap_of_comp (M : ModuleCat.{0} R)
    {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {A : Set X} {B : Set Y} {C : Set Z}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M (f ≫ g) (hg.comp hf) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M g hg ≫ AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M f hf :=
  (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp M f g hf hg).symm

theorem relativeSingularCohomologyMap_of_comp (M : ModuleCat.{0} R)
    {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {A : Set X} {B : Set Y} {C : Set Z}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (f ≫ g) (hg.comp hf) n =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M g hg n ≫ AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f hf n :=
  (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp M f g hf hg n).symm

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainFunctoriality.Cohomology
