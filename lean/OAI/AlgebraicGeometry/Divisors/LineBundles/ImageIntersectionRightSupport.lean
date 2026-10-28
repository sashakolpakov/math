import OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo

/-! # Image Intersection Right Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ImageIntersectionRightSupport.BundleCycles

noncomputable section

/-! Replacing the parametrization of an equal right support preserves the actual intersection cup under the corresponding identity pair maps. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Restriction

variable {M P Q N : Type} [TopologicalSpace N]
  (u : M → N) (v : P → N) (w : Q → N) (hw : Set.range w = Set.range v)

include hw in
theorem imageRightSupport_mapsTo : Set.MapsTo (𝟙 (TopCat.of N)) (Set.range w)ᶜ (Set.range v)ᶜ := by
  intro x hx
  rwa [← hw]

include hw in
theorem imageIntersectionRightSupport_mapsTo : Set.MapsTo (𝟙 (TopCat.of N))
    (Set.range u ∩ Set.range w)ᶜ (Set.range u ∩ Set.range v)ᶜ := by
  intro x hx
  rwa [← hw]

theorem imageIntersectionCup_rightSupport
    (hu : IsOpen (Set.range u)ᶜ) (hv : IsOpen (Set.range v)ᶜ) (hwopen : IsOpen (Set.range w)ᶜ) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range v)ᶜ (2 * q)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of N))
      (imageIntersectionRightSupport_mapsTo u v w hw) (2 * (p + q))
      (CycleClass.Thom.ImageIntersectionCup.Constructions.imageIntersectionCup u v hu hv p q a b) =
    CycleClass.Thom.ImageIntersectionCup.Constructions.imageIntersectionCup u w hu hwopen p q a
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of N))
        (imageRightSupport_mapsTo v w hw) (2 * q) b) := by
  have h := CycleClass.Thom.ImageIntersectionTo.Constructions.Restriction.imageIntersectionCup_restriction u v u w (𝟙 (TopCat.of N))
    (show Set.MapsTo (𝟙 (TopCat.of N)) (Set.range u)ᶜ (Set.range u)ᶜ from fun _ hx => hx)
    (imageRightSupport_mapsTo v w hw) hu hv hu hwopen p q a b
  have ha := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ (2 * p)) a
  exact h.trans (congrArg (fun c => CycleClass.Thom.ImageIntersectionCup.Constructions.imageIntersectionCup u w hu hwopen p q c
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of N))
      (imageRightSupport_mapsTo v w hw) (2 * q) b)) ha)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ImageIntersectionRightSupport.BundleCycles
