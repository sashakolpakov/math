import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.IntersectionCup
import OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup

/-! # Image Intersection To -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo
section

/-! Normal-coordinate multiplication for the actual image-supported
intersection cup, with its literal intersection complement. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions.Normal

open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.IntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Product.Constructions.Class
  ExteriorImageCup.Constructions ExteriorImageCup.Constructions.Restriction ExteriorImageCup.Constructions.Even

variable {M N P : Type} [TopologicalSpace N] (u : M → N) (v : P → N)

omit [TopologicalSpace N] in
theorem intersectionComplement_eq : (Set.range u)ᶜ ∪ (Set.range v)ᶜ =
    (Set.range u ∩ Set.range v)ᶜ := by
  ext x
  exact not_and_or.symm

theorem diagonalMapsTo_crossComplement : Set.MapsTo (ImageIntersectionCup.Constructions.diagonalMap (TopCat.of N))
    (Set.range u ∩ Set.range v)ᶜ
    (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of N) (TopCat.of N) (Set.range u)ᶜ (Set.range v)ᶜ) := by
  intro x hx
  apply Normal.IntersectionCup.Constructions.diagonalComplementMapsTo (TopCat.of N) (Set.range u)ᶜ (Set.range v)ᶜ
  rwa [intersectionComplement_eq]

theorem imageIntersectionCup_eq_even (hu : IsOpen (Set.range u)ᶜ) (hv : IsOpen (Set.range v)ᶜ)
    (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range v)ᶜ (2 * q)) :
    ImageIntersectionCup.Constructions.imageIntersectionCup u v hu hv p q a b =
    eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) S
      (2 * (p + q))) (intersectionComplement_eq u v))
      (Normal.IntersectionCup.Constructions.evenIntersectionCup (TopCat.of N) (Set.range u)ᶜ (Set.range v)ᶜ hu hv p q a b) := by
  have ht := Normal.Product.Constructions.Class.relativeCohomologyMap_targetCast (ImageIntersectionCup.Constructions.diagonalMap (TopCat.of N))
    (ExteriorImageCup.Constructions.crossSupportComplement_range u v) (diagonalMapsTo_crossComplement u v)
    (ImageIntersectionCup.Constructions.diagonalMap_complement u v) (2 * (p + q))
    (ExteriorImageCup.Constructions.Even.evenExteriorCup (TopCat.of N) (TopCat.of N) (Set.range u)ᶜ (Set.range v)ᶜ hu hv p q a b)
  have hs := ExteriorImageCup.Constructions.Restriction.relativeCohomologyMap_sourceCast (ImageIntersectionCup.Constructions.diagonalMap (TopCat.of N))
    (intersectionComplement_eq u v) (Normal.IntersectionCup.Constructions.diagonalComplementMapsTo (TopCat.of N) (Set.range u)ᶜ (Set.range v)ᶜ)
    (diagonalMapsTo_crossComplement u v) (2 * (p + q))
    (ExteriorImageCup.Constructions.Even.evenExteriorCup (TopCat.of N) (TopCat.of N) (Set.range u)ᶜ (Set.range v)ᶜ hu hv p q a b)
  exact ht.trans hs.symm

variable {p q : ℕ}
  (f : TopCat.of N ⟶ TopCat.of (Fin p → ℂ)) (g : TopCat.of N ⟶ TopCat.of (Fin q → ℂ))
  (hf : Set.MapsTo f (Set.range u)ᶜ ({0}ᶜ)) (hg : Set.MapsTo g (Set.range v)ᶜ ({0}ᶜ))
  (e : ((Fin p → ℂ) × (Fin q → ℂ)) ≃L[ℂ] (Fin (p + q) → ℂ))

include hf hg in
theorem intersectionNormalMapsTo : Set.MapsTo (Normal.IntersectionCup.Constructions.internalNormalMap f g e)
    (Set.range u ∩ Set.range v)ᶜ ({0}ᶜ) := by
  intro x hx
  apply Normal.IntersectionCup.Constructions.internalNormalMapsTo f g hf hg e
  rwa [intersectionComplement_eq]

theorem imageIntersectionCup_normalized_pullbacks
    (hu : IsOpen (Set.range u)ᶜ) (hv : IsOpen (Set.range v)ᶜ) :
    ImageIntersectionCup.Constructions.imageIntersectionCup u v hu hv p q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf (2 * p) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg (2 * q) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q)) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Normal.IntersectionCup.Constructions.internalNormalMap f g e)
      (intersectionNormalMapsTo u v f g hf hg e) (2 * (p + q)) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (p + q)) := by
  rw [imageIntersectionCup_eq_even, Normal.IntersectionCup.Constructions.evenIntersectionCup_normalized_pullbacks f g hf hg e hu hv]
  exact ExteriorImageCup.Constructions.Restriction.relativeCohomologyMap_sourceCast (Normal.IntersectionCup.Constructions.internalNormalMap f g e) (intersectionComplement_eq u v)
    (Normal.IntersectionCup.Constructions.internalNormalMapsTo f g hf hg e) (intersectionNormalMapsTo u v f g hf hg e)
    (2 * (p + q)) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (p + q))

end Constructions.Normal

end

/-! The actual supported intersection cup commutes with maps preserving
the two support complements, in particular with genuine neighborhood restrictions. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions.Restriction

open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Normal OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions
  ExteriorImageCup.Constructions.Restriction Normal.IntersectionCup.Constructions ExteriorImageCup.Constructions.Even

theorem diagonal_square {X Y : TopCat.{0}} (f : X ⟶ Y) :
    f ≫ ImageIntersectionCup.Constructions.diagonalMap Y = ImageIntersectionCup.Constructions.diagonalMap X ≫ AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, f) : (X, X) ⟶ (Y, Y)) := by
  ext x <;> rfl

variable {M P L K N N' : Type} [TopologicalSpace N] [TopologicalSpace N']
  (u : M → N) (v : P → N) (w : L → N') (z : K → N')
  (f : TopCat.of N' ⟶ TopCat.of N)
  (hf : Set.MapsTo f (Set.range w)ᶜ (Set.range u)ᶜ)
  (hg : Set.MapsTo f (Set.range z)ᶜ (Set.range v)ᶜ)

include hf hg in
theorem intersectionMapsTo : Set.MapsTo f (Set.range w ∩ Set.range z)ᶜ
    (Set.range u ∩ Set.range v)ᶜ := by
  intro x hx h
  rw [← Normal.intersectionComplement_eq w z] at hx
  rcases hx with hx | hx
  · exact hf hx h.1
  · exact hg hx h.2

theorem imageIntersectionCup_restriction
    (hu : IsOpen (Set.range u)ᶜ) (hv : IsOpen (Set.range v)ᶜ)
    (hw : IsOpen (Set.range w)ᶜ) (hz : IsOpen (Set.range z)ᶜ) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range v)ᶜ (2 * q)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f (intersectionMapsTo u v w z f hf hg)
      (2 * (p + q)) (ImageIntersectionCup.Constructions.imageIntersectionCup u v hu hv p q a b) =
    ImageIntersectionCup.Constructions.imageIntersectionCup w z hw hz p q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf (2 * p) a)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hg (2 * q) b) := by
  let Q := ModuleCat.of ℚ ℚ
  let f₂ := AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, f) : (TopCat.of N', TopCat.of N') ⟶ (TopCat.of N, TopCat.of N))
  have h₁ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp Q f (ImageIntersectionCup.Constructions.diagonalMap (TopCat.of N))
    (intersectionMapsTo u v w z f hf hg) (ImageIntersectionCup.Constructions.diagonalMap_complement u v) (2 * (p + q))
  have h₂ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp Q (ImageIntersectionCup.Constructions.diagonalMap (TopCat.of N')) f₂
    (Normal.diagonalMapsTo_crossComplement w z) (ExteriorImageCup.Constructions.imageProductMapsTo u v f f hf hg) (2 * (p + q))
  have he := ConcreteCategory.congr_hom (h₁.trans h₂.symm) (ExteriorImageCup.Constructions.imageExteriorCup u v hu hv p q a b)
  have hn := ExteriorImageCup.Constructions.imageExteriorCup_naturality u v f f hf hg hw hz hu hv p q a b
  have hc := congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (ImageIntersectionCup.Constructions.diagonalMap (TopCat.of N'))
    (Normal.diagonalMapsTo_crossComplement w z) (2 * (p + q))) hn
  have hs := ExteriorImageCup.Constructions.Restriction.relativeCohomologyMap_sourceCast (ImageIntersectionCup.Constructions.diagonalMap (TopCat.of N'))
    (Normal.intersectionComplement_eq w z) (Normal.IntersectionCup.Constructions.diagonalComplementMapsTo (TopCat.of N') (Set.range w)ᶜ (Set.range z)ᶜ)
    (Normal.diagonalMapsTo_crossComplement w z) (2 * (p + q))
    (ExteriorImageCup.Constructions.Even.evenExteriorCup (TopCat.of N') (TopCat.of N') (Set.range w)ᶜ (Set.range z)ᶜ hw hz p q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q f hf (2 * p) a)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q f hg (2 * q) b))
  exact he.trans (hc.trans (hs.symm.trans (Normal.imageIntersectionCup_eq_even w z hw hz p q _ _).symm))

end Constructions.Restriction

end AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo

namespace AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport

/-! The literal inverse image of a support, presented as the image of its
subtype inclusion, with its actual complement pair map. -/

open _root_.CategoryTheory

variable {X Y : TopCat.{0}} {L : Type} (f : X ⟶ Y) (v : L → Y)

def pulledBackImage : (f ⁻¹' Set.range v) → X := Subtype.val

theorem pulledBackImage_range : Set.range (pulledBackImage f v) = f ⁻¹' Set.range v :=
  Subtype.range_coe

theorem pulledBackImage_complement : (Set.range (pulledBackImage f v))ᶜ = f ⁻¹' (Set.range v)ᶜ := by
  rw [pulledBackImage_range]
  rfl

theorem pulledBackImage_mapsTo : Set.MapsTo f (Set.range (pulledBackImage f v))ᶜ (Set.range v)ᶜ := by
  intro x hx
  exact (Set.ext_iff.mp (pulledBackImage_complement f v) x).mp hx

theorem pulledBackImage_openComplement (hv : IsOpen (Set.range v)ᶜ) :
    IsOpen (Set.range (pulledBackImage f v))ᶜ := by
  rw [pulledBackImage_complement]
  exact hv.preimage f.hom.continuous

end AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport

end

end OAI
