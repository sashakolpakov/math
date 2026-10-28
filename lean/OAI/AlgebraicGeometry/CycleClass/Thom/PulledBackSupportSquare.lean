import OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo
import OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction

/-! # Pulled Back Support Square -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PulledBackSupportSquare.Constructions

noncomputable section

/-! An actual commuting square identifies the literal pulled-back image
supports and the corresponding supported cohomology pullbacks. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y Z T : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ T) (k : T ⟶ Z)
  (hs : f ≫ g = h ≫ k)

include hs in
theorem pulledBackImage_square_range {L : Type} (v : L → Z) :
    Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage f (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage g v)) =
      Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage h (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage k v)) := by
  simp only [ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_range]
  ext x
  change g (f x) ∈ Set.range v ↔ k (h x) ∈ Set.range v
  exact Iff.of_eq (congrArg (fun y => y ∈ Set.range v) (ConcreteCategory.congr_hom hs x))

include hs in
theorem relativePullback_square {A : Set X} {B : Set Y} {C : Set T} {D : Set Z}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B D)
    (hh : Set.MapsTo h A C) (hk : Set.MapsTo k C D) (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Z D n) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf n
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg n a) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) h hh n
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) k hk n a) := by
  have hfg := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) f g hf hg n
  have hhk := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) h k hh hk n
  have hc := ThomOpenRestriction.Constructions.pairMap_congr hs (fun _ hx => hg (hf hx)) (fun _ hx => hk (hh hx)) n
  exact ConcreteCategory.congr_hom (hfg.trans (hc.trans hhk.symm)) a

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PulledBackSupportSquare.Constructions
