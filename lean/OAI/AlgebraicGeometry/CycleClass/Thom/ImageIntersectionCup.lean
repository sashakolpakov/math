import OAI.AlgebraicGeometry.CycleClass.Thom.AbsoluteProductMaps

/-! # Image Intersection Cup -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions

/-! Pulling an actual supported exterior cup through the diagonal gives
a class supported on the intersection of the two images. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorCupForget.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.AbsoluteProductMaps.Constructions
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def diagonalMap (X : TopCat.{0}) : X ⟶ TopCat.of (X × X) :=
  TopCat.ofHom ⟨fun x => (x, x), continuous_id.prodMk continuous_id⟩

theorem diagonalMap_fst (X : TopCat.{0}) : diagonalMap X ≫ TopCat.prodFst = 𝟙 X := rfl
theorem diagonalMap_snd (X : TopCat.{0}) : diagonalMap X ≫ TopCat.prodSnd = 𝟙 X := rfl

variable {M N P : Type} [TopologicalSpace N] (u : M → N) (v : P → N)

theorem diagonalMap_complement : Set.MapsTo (diagonalMap (TopCat.of N))
    (Set.range u ∩ Set.range v)ᶜ (Set.range (Prod.map u v))ᶜ := by
  intro x hx h
  apply hx
  obtain ⟨⟨a, b⟩, hab⟩ := h
  exact ⟨⟨a, congrArg Prod.fst hab⟩, ⟨b, congrArg Prod.snd hab⟩⟩

def imageIntersectionCup (hu : IsOpen (Set.range u)ᶜ) (hv : IsOpen (Set.range v)ᶜ)
    (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range v)ᶜ (2 * q)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range u ∩ Set.range v)ᶜ (2 * (p + q)) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (diagonalMap (TopCat.of N))
    (diagonalMap_complement u v) (2 * (p + q)) (ExteriorImageCup.Constructions.imageExteriorCup u v hu hv p q a b)

theorem imageIntersectionCup_forget (hu : IsOpen (Set.range u)ᶜ) (hv : IsOpen (Set.range v)ᶜ)
    (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range v)ᶜ (2 * q)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of N)
      (Set.range u ∩ Set.range v)ᶜ (2 * (p + q)) (imageIntersectionCup u v hu hv p q a b) =
    eqToHom (congrArg (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N))
      (Nat.mul_add 2 p q).symm)
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (TopCat.of N) (2 * p) (2 * q)
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ (2 * p) a)
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range v)ᶜ (2 * q) b)) := by
  unfold imageIntersectionCup
  rw [ExteriorCupForget.Constructions.relativeInclusion_pullback, ExteriorCupForget.Constructions.imageExteriorCup_forget, AbsoluteProductMaps.Constructions.evenAbsoluteExteriorCup_pullback,
    diagonalMap_fst, diagonalMap_snd, AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id, AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id,
    ConcreteCategory.id_apply, ConcreteCategory.id_apply]

end AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions.Linearity

/-! Linearity of the actual image-supported intersection cup in both
arguments, ready for finite sums of original cycle generators. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Even

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N L : Type} [TopologicalSpace N] (u : M → N) (v : L → N)
  (hu : IsOpen (Set.range u)ᶜ) (hv : IsOpen (Set.range v)ᶜ) (p q : ℕ)

local notation "A" => OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ (2 * p)
local notation "B" => OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range v)ᶜ (2 * q)
local notation "C" => OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u ∩ Set.range v)ᶜ (2 * (p + q))

theorem imageIntersectionCup_add_left (a a' : A) (b : B) :
    imageIntersectionCup u v hu hv p q (a + a') b =
      imageIntersectionCup u v hu hv p q a b + imageIntersectionCup u v hu hv p q a' b := by
  simp only [imageIntersectionCup, ExteriorImageCup.Constructions.imageExteriorCup, ExteriorImageCup.Constructions.Even.evenExteriorCup, HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup,
    map_add, LinearMap.add_apply]

theorem imageIntersectionCup_smul_left (r : ℚ) (a : A) (b : B) :
    imageIntersectionCup u v hu hv p q (r • a) b = r • imageIntersectionCup u v hu hv p q a b := by
  simp only [imageIntersectionCup, ExteriorImageCup.Constructions.imageExteriorCup, ExteriorImageCup.Constructions.Even.evenExteriorCup, HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup,
    map_smul, LinearMap.smul_apply]

theorem imageIntersectionCup_add_right (a : A) (b b' : B) :
    imageIntersectionCup u v hu hv p q a (b + b') =
      imageIntersectionCup u v hu hv p q a b + imageIntersectionCup u v hu hv p q a b' := by
  simp only [imageIntersectionCup, ExteriorImageCup.Constructions.imageExteriorCup, ExteriorImageCup.Constructions.Even.evenExteriorCup, HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup, map_add]

theorem imageIntersectionCup_smul_right (r : ℚ) (a : A) (b : B) :
    imageIntersectionCup u v hu hv p q a (r • b) = r • imageIntersectionCup u v hu hv p q a b := by
  simp only [imageIntersectionCup, ExteriorImageCup.Constructions.imageExteriorCup, ExteriorImageCup.Constructions.Even.evenExteriorCup, HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup, map_smul]

def imageIntersectionCupLinear : A →ₗ[ℚ] B →ₗ[ℚ] C where
  toFun a :=
    { toFun := imageIntersectionCup u v hu hv p q a
      map_add' := imageIntersectionCup_add_right u v hu hv p q a
      map_smul' r b := imageIntersectionCup_smul_right u v hu hv p q r a b }
  map_add' a a' := by
    ext b
    exact imageIntersectionCup_add_left u v hu hv p q a a' b
  map_smul' r a := by
    ext b
    exact imageIntersectionCup_smul_left u v hu hv p q r a b

end AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions.Linearity

end

end OAI
