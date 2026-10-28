import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Product

/-! # Exterior Image Cup -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Even

/-! The actual exterior cup in degree twice the sum, with its naturality
under actual maps of pairs. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Product.Constructions.Class

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def evenExteriorCup (X Y : TopCat.{0}) (A : Set X) (B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B (2 * q)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × Y))
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) (2 * (p + q)) :=
  eqToHom (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of (X × Y)) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) n) (Nat.mul_add 2 p q).symm)
    (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y A B hA hB (2 * p) (2 * q) a b)

theorem evenExteriorCup_naturality {X X' Y Y' : TopCat.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y')
    {A : Set X} {A' : Set X'} {B : Set Y} {B' : Set Y'}
    (hf : Set.MapsTo f A A') (hg : Set.MapsTo g B B')
    (hA : IsOpen A) (hB : IsOpen B) (hA' : IsOpen A') (hB' : IsOpen B') (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X' A' (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y' B' (2 * q)) :
    evenExteriorCup X Y A B hA hB p q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf (2 * p) a)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg (2 * q) b) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (X', Y')))
      (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.crossSupportComplement_mapsTo f g hf hg) (2 * (p + q))
      (evenExteriorCup X' Y' A' B' hA' hB' p q a b) := by
  unfold evenExteriorCup
  rw [HodgeConjecture.DegreeTwo.ExteriorCupNaturality.Constructions.relativeExteriorCup_naturality f g hf hg hA hB hA' hB' (2 * p) (2 * q) a b]
  exact Normal.Product.Constructions.Class.relativeCohomologyMap_degreeCast
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (X', Y')))
    (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.crossSupportComplement_mapsTo f g hf hg) (Nat.mul_add 2 p q).symm _

end AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Even

namespace AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions

/-! The exterior cup supported in the actual image of a product map, and
its restriction under actual maps into the two factors. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Product.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Even

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N M' N' : Type} [TopologicalSpace N] [TopologicalSpace N']
  (u : M → N) (v : M' → N')

theorem crossSupportComplement_range :
    HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of N) (TopCat.of N') (Set.range u)ᶜ (Set.range v)ᶜ =
      (Set.range (Prod.map u v))ᶜ := by
  classical
  ext z
  change (z.1 ∉ Set.range u ∨ z.2 ∉ Set.range v) ↔ z ∉ Set.range (Prod.map u v)
  simp only [Set.range_prodMap, Set.mem_prod, not_and_or]

def imageExteriorCup (hu : IsOpen (Set.range u)ᶜ) (hv : IsOpen (Set.range v)ᶜ)
    (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N') (Set.range v)ᶜ (2 * q)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (N × N'))
      (Set.range (Prod.map u v))ᶜ (2 * (p + q)) :=
  eqToHom (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of (N × N')) A (2 * (p + q))) (crossSupportComplement_range u v))
    (Even.evenExteriorCup (TopCat.of N) (TopCat.of N') (Set.range u)ᶜ (Set.range v)ᶜ hu hv p q a b)

variable {X Y : TopCat.{0}} (f : X ⟶ TopCat.of N) (g : Y ⟶ TopCat.of N')
  {A : Set X} {B : Set Y} (hf : Set.MapsTo f A (Set.range u)ᶜ)
  (hg : Set.MapsTo g B (Set.range v)ᶜ)

include hf hg in
theorem imageProductMapsTo :
    Set.MapsTo (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (TopCat.of N, TopCat.of N')))
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) (Set.range (Prod.map u v))ᶜ := by
  have h := HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.crossSupportComplement_mapsTo f g hf hg
  rw [crossSupportComplement_range u v] at h
  exact h

theorem imageExteriorCup_naturality (hA : IsOpen A) (hB : IsOpen B)
    (hu : IsOpen (Set.range u)ᶜ) (hv : IsOpen (Set.range v)ᶜ) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N') (Set.range v)ᶜ (2 * q)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (TopCat.of N, TopCat.of N')))
      (imageProductMapsTo u v f g hf hg) (2 * (p + q))
      (imageExteriorCup u v hu hv p q a b) =
    Even.evenExteriorCup X Y A B hA hB p q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf (2 * p) a)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg (2 * q) b) := by
  have h := Normal.Product.Constructions.Class.relativeCohomologyMap_targetCast
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (TopCat.of N, TopCat.of N')))
    (crossSupportComplement_range u v) (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.crossSupportComplement_mapsTo f g hf hg)
    (imageProductMapsTo u v f g hf hg) (2 * (p + q))
    (Even.evenExteriorCup (TopCat.of N) (TopCat.of N') (Set.range u)ᶜ (Set.range v)ᶜ hu hv p q a b)
  exact h.trans (Even.evenExteriorCup_naturality f g hf hg hA hB hu hv p q a b).symm

end AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Restriction

/-! Restriction of the actual exterior cup with both source and target
supports written as images of the genuine product maps. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

open OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem relativeCohomologyMap_sourceCast {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A A' : Set X} {B : Set Y} (he : A = A')
    (h : Set.MapsTo f A B) (h' : Set.MapsTo f A' B) (n : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B n) :
    eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n) he)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f h n b) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f h' n b := by
  subst A'
  rfl

variable {M M' N N' X Y L L' : Type}
  [TopologicalSpace N] [TopologicalSpace N'] [TopologicalSpace X] [TopologicalSpace Y]
  (u : M → X) (v : M' → Y) (w : L → N) (z : L' → N')
  (f : TopCat.of X ⟶ TopCat.of N) (g : TopCat.of Y ⟶ TopCat.of N')
  (hf : Set.MapsTo f (Set.range u)ᶜ (Set.range w)ᶜ)
  (hg : Set.MapsTo g (Set.range v)ᶜ (Set.range z)ᶜ)

include hf hg in
theorem productImageRestrictionMapsTo :
    Set.MapsTo (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (TopCat.of X, TopCat.of Y) ⟶ (TopCat.of N, TopCat.of N')))
      (Set.range (Prod.map u v))ᶜ (Set.range (Prod.map w z))ᶜ := by
  have h := imageProductMapsTo w z f g hf hg
  rw [crossSupportComplement_range u v] at h
  exact h

theorem imageExteriorCup_restriction
    (hu : IsOpen (Set.range u)ᶜ) (hv : IsOpen (Set.range v)ᶜ)
    (hw : IsOpen (Set.range w)ᶜ) (hz : IsOpen (Set.range z)ᶜ) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range w)ᶜ (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N') (Set.range z)ᶜ (2 * q)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (TopCat.of X, TopCat.of Y) ⟶ (TopCat.of N, TopCat.of N')))
      (productImageRestrictionMapsTo u v w z f g hf hg) (2 * (p + q))
      (imageExteriorCup w z hw hz p q a b) =
    imageExteriorCup u v hu hv p q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf (2 * p) a)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg (2 * q) b) := by
  have h := imageExteriorCup_naturality w z f g hf hg hu hv hw hz p q a b
  have hc := congrArg (eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of (X × Y)) S (2 * (p + q))) (crossSupportComplement_range u v))) h
  have hs := relativeCohomologyMap_sourceCast
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (TopCat.of X, TopCat.of Y) ⟶ (TopCat.of N, TopCat.of N')))
    (crossSupportComplement_range u v) (imageProductMapsTo w z f g hf hg)
    (productImageRestrictionMapsTo u v w z f g hf hg) (2 * (p + q))
    (imageExteriorCup w z hw hz p q a b)
  exact hs.symm.trans hc

end AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Restriction

end

end OAI
