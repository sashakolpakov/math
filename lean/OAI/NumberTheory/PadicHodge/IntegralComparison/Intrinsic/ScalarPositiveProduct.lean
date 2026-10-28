import OAI.NumberTheory.PadicHodge.IntegralComparison.GradedPositiveMultilinear
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechScalarCoordinates
import Mathlib.RingTheory.Flat.Basic

/-! # Scalar Positive Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ScalarPositiveProduct

noncomputable section

/-! Nonzero positive-degree products descend through the actual scalar
comparison by tensor spanning, and ascend through injective scalar units. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
  {ι : Type} [Finite ι] (U : ι → X.left.Opens)

abbrev inverseCover : ι → Y.left.Opens := fun i => f ⁻¹ᵁ U i

local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.CechProduct.total R X (OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U)
local notation "B" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.CechProduct.total S Y (OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ScalarPositiveProduct.inverseCover R S X Y f U))
local notation "μ" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.CechProduct.cohomologyCup R X (OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U)
local notation "ν" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.CechProduct.cohomologyCup S Y (OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ScalarPositiveProduct.inverseCover R S X Y f U))

abbrev map := IntrinsicDeRham.CechScalarProduct.Intrinsic.homologyMap R S X Y f h U

theorem natural (n : ℕ) (v : Fin (n+1) → (A).homology 1) :
    ScalarPositiveProduct.map R S X Y f h U (n+1) (GradedPositiveProduct.product (fun i j x y => μ i j x y) n v) =
      GradedPositiveProduct.product (fun i j x y => ν i j x y) n
        (fun i => ScalarPositiveProduct.map R S X Y f h U 1 (v i)) :=
  GradedPositiveProduct.natural (fun i j x y => μ i j x y) (fun i j x y => ν i j x y)
    (fun i => ScalarPositiveProduct.map R S X Y f h U i)
    (IntrinsicDeRham.CechScalarProduct.Intrinsic.homologyMap_cup R S X Y f h U) n v

theorem pure_input_detection [IsIso (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.homologyMap R S X Y f h U 1)]
    (n : ℕ) (hn : ∃ v : Fin (n+1) → (B).homology 1,
      GradedPositiveProduct.product (fun i j x y => ν i j x y) n v ≠ 0) :
    ∃ v : Fin (n+1) → (A).homology 1,
      GradedPositiveProduct.product (fun i j x y => ν i j x y) n
        (fun i => ScalarPositiveProduct.map R S X Y f h U 1 (v i)) ≠ 0 := by
  have hd := GradedPositiveMultilinear.scalar_exists_nonzero ν
    (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.homologyMap R S X Y f h U 1).hom
    (ConcreteCategory.bijective_of_isIso (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.homologyMap R S X Y f h U 1)).surjective
    n hn
  dsimp only [ScalarPositiveProduct.map]
  rw [IntrinsicDeRham.CechScalarCoordinates.Intrinsic.homologyMap]
  exact hd

theorem image_exists_nonzero [IsIso (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.homologyMap R S X Y f h U 1)]
    (n : ℕ) (hn : ∃ v : Fin (n+1) → (B).homology 1,
      GradedPositiveProduct.product (fun i j x y => ν i j x y) n v ≠ 0) :
    ∃ v : Fin (n+1) → (A).homology 1,
      ScalarPositiveProduct.map R S X Y f h U (n+1)
        (GradedPositiveProduct.product (fun i j x y => μ i j x y) n v) ≠ 0 := by
  obtain ⟨v, hv⟩ := pure_input_detection R S X Y f h U n hn
  exact ⟨v, fun hz => hv ((natural R S X Y f h U n v).symm.trans hz)⟩

theorem source_exists_nonzero [IsIso (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.homologyMap R S X Y f h U 1)]
    (n : ℕ) (hn : ∃ v : Fin (n+1) → (B).homology 1,
      GradedPositiveProduct.product (fun i j x y => ν i j x y) n v ≠ 0) :
    ∃ v : Fin (n+1) → (A).homology 1,
      GradedPositiveProduct.product (fun i j x y => μ i j x y) n v ≠ 0 := by
  obtain ⟨v, hv⟩ := image_exists_nonzero R S X Y f h U n hn
  exact ⟨v, fun hz => hv ((congrArg (ScalarPositiveProduct.map R S X Y f h U (n+1)) hz).trans (map_zero _))⟩

theorem injective (n : ℕ) [Module.Flat R ((A).homology n)] [FaithfulSMul R S]
    [IsIso (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.homologyMap R S X Y f h U n)] :
    Function.Injective (ScalarPositiveProduct.map R S X Y f h U n) := by
  dsimp only [ScalarPositiveProduct.map]
  rw [IntrinsicDeRham.CechScalarCoordinates.Intrinsic.homologyMap]
  exact (ConcreteCategory.bijective_of_isIso
    (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.homologyMap R S X Y f h U n)).injective.comp
      (Module.Flat.tensorProduct_mk_injective R ((A).homology n) S)

theorem target_exists_nonzero (n : ℕ) [Module.Flat R ((A).homology (n+1))] [FaithfulSMul R S]
    [IsIso (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.homologyMap R S X Y f h U (n+1))]
    (hn : ∃ v : Fin (n+1) → (A).homology 1,
      GradedPositiveProduct.product (fun i j x y => μ i j x y) n v ≠ 0) :
    ∃ v : Fin (n+1) → (B).homology 1,
      GradedPositiveProduct.product (fun i j x y => ν i j x y) n v ≠ 0 := by
  obtain ⟨v, hv⟩ := hn
  refine ⟨fun i => ScalarPositiveProduct.map R S X Y f h U 1 (v i), ?_⟩
  intro hz
  apply hv
  apply ScalarPositiveProduct.injective R S X Y f h U (n+1)
  exact (natural R S X Y f h U n v).trans (hz.trans (map_zero _).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ScalarPositiveProduct
