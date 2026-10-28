import OAI.AlgebraicGeometry.Resolution.Blowups.ChartLift
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Chart Flat Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ChartFlatBaseChange.Construction

noncomputable section

/-! Flat base change of actual affine blowup chart rings. -/

open TensorProduct _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Flat scalar extension preserves regular elements. -/
theorem flat_algebraMap_regular [Module.Flat R S] (c : R) (hc : IsRegular c) :
    IsRegular (algebraMap R S c) := by
  have hs : IsSMulRegular S c := Module.Flat.isSMulRegular_of_isRegular hc
  have hl : IsLeftRegular (algebraMap R S c) := by
    change Function.Injective (fun x : S => algebraMap R S c * x)
    simpa only [IsSMulRegular, Algebra.smul_def] using hs
  exact ⟨hl, fun x y h => hl (by simpa only [mul_comm _ (algebraMap R S c)] using h)⟩

/-- The coefficient algebra structure used for tensoring an affine blowup chart. -/
abbrev blowupChartAlgebra {A : Type u} [CommRing A] (I : Ideal A) (a : I) :
    Algebra A (Blowup.Charts.Construction.blowupChart I a) := (Blowup.Charts.Construction.blowupChartConstants I a).toAlgebra

attribute [local instance] blowupChartAlgebra

variable (I : Ideal R) (a : I)

abbrev blowupChartTensor := Blowup.Charts.Construction.blowupChart I a ⊗[R] S

def blowupChartTensorLeft : Blowup.Charts.Construction.blowupChart I a →+* blowupChartTensor (S := S) I a :=
  Algebra.TensorProduct.includeLeftRingHom

def blowupChartTensorRight : S →+* blowupChartTensor (S := S) I a :=
  Algebra.TensorProduct.includeRight.toRingHom

theorem blowupChartTensor_compat (r : R) :
    blowupChartTensorLeft (S := S) I a (Blowup.Charts.Construction.blowupChartConstants I a r) =
      blowupChartTensorRight (S := S) I a (algebraMap R S r) := by
  exact congrArg (fun f : R →+* blowupChartTensor (S := S) I a => f r)
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := R) (A := Blowup.Charts.Construction.blowupChart I a) (B := S))

abbrev blowupBaseChangeElement : I.map (algebraMap R S) :=
  ⟨algebraMap R S a.val, Ideal.mem_map_of_mem (algebraMap R S) a.property⟩

abbrev blowupBaseChangedChart :=
  Blowup.Charts.Construction.blowupChart (I.map (algebraMap R S)) (blowupBaseChangeElement (S := S) I a)

theorem blowupChartTensor_center :
    (I.map (algebraMap R S)).map (blowupChartTensorRight (S := S) I a) =
      Ideal.span {blowupChartTensorRight (S := S) I a (algebraMap R S a.val)} := by
  have he : (blowupChartTensorRight (S := S) I a).comp (algebraMap R S) =
      (blowupChartTensorLeft (S := S) I a).comp (Blowup.Charts.Construction.blowupChartConstants I a) := by
    apply RingHom.ext
    intro r
    exact (blowupChartTensor_compat I a r).symm
  rw [Ideal.map_map, he, ← Ideal.map_map, ExceptionalIdeal.Construction.blowupChart_extendedIdeal, Ideal.map_span,
    Set.image_singleton, blowupChartTensor_compat]

theorem blowupChartTensor_parameter_regular [Module.Flat R S] :
    IsRegular (blowupChartTensorRight (S := S) I a (algebraMap R S a.val)) := by
  have h := flat_algebraMap_regular (R := Blowup.Charts.Construction.blowupChart I a) (S := blowupChartTensor (S := S) I a)
    (Blowup.Charts.Construction.blowupChartConstants I a a.val) (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a)
  change IsRegular (blowupChartTensorLeft (S := S) I a (Blowup.Charts.Construction.blowupChartConstants I a a.val)) at h
  rwa [blowupChartTensor_compat] at h

/-- Flatness makes the chosen parameter regular on the tensor product,
so the chart universal property gives the reverse comparison map. -/
def blowupChartToTensor [Module.Flat R S] :
    blowupBaseChangedChart (S := S) I a →+* blowupChartTensor (S := S) I a :=
  ChartLift.Construction.blowupChartLift (I.map (algebraMap R S)) (blowupBaseChangeElement I a)
    (blowupChartTensorRight (S := S) I a) (blowupChartTensor_center I a)
    (blowupChartTensor_parameter_regular I a)

theorem blowupChartToTensor_constants [Module.Flat R S] (s : S) :
    blowupChartToTensor I a
      (Blowup.Charts.Construction.blowupChartConstants (I.map (algebraMap R S)) (blowupBaseChangeElement I a) s) =
      blowupChartTensorRight (S := S) I a s :=
  ChartLift.Construction.blowupChartLift_constants (I.map (algebraMap R S)) (blowupBaseChangeElement I a)
    (blowupChartTensorRight (S := S) I a) (blowupChartTensor_center I a)
    (blowupChartTensor_parameter_regular I a) s

local instance : Algebra R (blowupBaseChangedChart (S := S) I a) :=
  ((Blowup.Charts.Construction.blowupChartConstants (I.map (algebraMap R S)) (blowupBaseChangeElement I a)).comp
    (algebraMap R S)).toAlgebra

/-- The coefficient-extension chart map as a base-algebra homomorphism. -/
def blowupTensorChartMap : Blowup.Charts.Construction.blowupChart I a →ₐ[R] blowupBaseChangedChart (S := S) I a where
  toRingHom := ChartLift.Construction.blowupChartMap I (algebraMap R S) a
  commutes' r := ChartLift.Construction.blowupChartMap_constants I (algebraMap R S) a r

def blowupBaseChangeConstants : S →ₐ[R] blowupBaseChangedChart (S := S) I a where
  toRingHom := Blowup.Charts.Construction.blowupChartConstants (I.map (algebraMap R S)) (blowupBaseChangeElement I a)
  commutes' _ := rfl

/-- The forward comparison is the tensor product's universal map. -/
def blowupTensorToChart : blowupChartTensor (S := S) I a →+* blowupBaseChangedChart (S := S) I a :=
  (Algebra.TensorProduct.lift (blowupTensorChartMap (S := S) I a)
    (blowupBaseChangeConstants (S := S) I a)
    (fun x y => mul_comm (blowupTensorChartMap (S := S) I a x)
      (blowupBaseChangeConstants (S := S) I a y))).toRingHom

theorem blowupTensorToChart_left (x : Blowup.Charts.Construction.blowupChart I a) :
    blowupTensorToChart (S := S) I a (blowupChartTensorLeft (S := S) I a x) =
      ChartLift.Construction.blowupChartMap I (algebraMap R S) a x := by
  simp [blowupTensorToChart, blowupChartTensorLeft, Algebra.TensorProduct.lift_tmul,
    blowupTensorChartMap]
  exact mul_one (ChartLift.Construction.blowupChartMap I (algebraMap R S) a x)

theorem blowupTensorToChart_right (s : S) :
    blowupTensorToChart (S := S) I a (blowupChartTensorRight (S := S) I a s) =
      Blowup.Charts.Construction.blowupChartConstants (I.map (algebraMap R S)) (blowupBaseChangeElement I a) s := by
  simp [blowupTensorToChart, blowupChartTensorRight, Algebra.TensorProduct.lift_tmul,
    blowupBaseChangeConstants]
  exact one_mul (Blowup.Charts.Construction.blowupChartConstants (I.map (algebraMap R S)) (blowupBaseChangeElement I a) s)

theorem blowupChartToTensor_chartMap [Module.Flat R S] :
    (blowupChartToTensor (S := S) I a).comp (ChartLift.Construction.blowupChartMap I (algebraMap R S) a) =
      blowupChartTensorLeft (S := S) I a := by
  apply ChartLift.Construction.blowupChart_hom_ext I a
    ((blowupChartTensorRight (S := S) I a).comp (algebraMap R S))
    (blowupChartTensor_parameter_regular I a)
  · intro r
    change blowupChartToTensor I a (ChartLift.Construction.blowupChartMap I (algebraMap R S) a
      (Blowup.Charts.Construction.blowupChartConstants I a r)) = _
    rw [ChartLift.Construction.blowupChartMap_constants]
    exact blowupChartToTensor_constants I a (algebraMap R S r)
  · intro r
    exact blowupChartTensor_compat I a r

theorem blowupChartToTensor_tensorToChart [Module.Flat R S] :
    (blowupChartToTensor (S := S) I a).comp (blowupTensorToChart (S := S) I a) =
      RingHom.id (blowupChartTensor (S := S) I a) := by
  apply Algebra.TensorProduct.ringHom_ext
  · apply RingHom.ext
    intro x
    change blowupChartToTensor I a
      (blowupTensorToChart I a (blowupChartTensorLeft (S := S) I a x)) =
        blowupChartTensorLeft (S := S) I a x
    rw [blowupTensorToChart_left]
    exact congrArg (fun f : Blowup.Charts.Construction.blowupChart I a →+* blowupChartTensor (S := S) I a => f x)
      (blowupChartToTensor_chartMap I a)
  · apply RingHom.ext
    intro s
    change blowupChartToTensor I a
      (blowupTensorToChart I a (blowupChartTensorRight (S := S) I a s)) =
        blowupChartTensorRight (S := S) I a s
    rw [blowupTensorToChart_right, blowupChartToTensor_constants]

theorem blowupTensorToChart_chartToTensor [Module.Flat R S] :
    (blowupTensorToChart (S := S) I a).comp (blowupChartToTensor (S := S) I a) =
      RingHom.id (blowupBaseChangedChart (S := S) I a) := by
  apply ChartLift.Construction.blowupChart_hom_ext (I.map (algebraMap R S)) (blowupBaseChangeElement I a)
    (Blowup.Charts.Construction.blowupChartConstants (I.map (algebraMap R S)) (blowupBaseChangeElement I a))
    (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular (I.map (algebraMap R S)) (blowupBaseChangeElement I a))
  · intro s
    change blowupTensorToChart I a (blowupChartToTensor I a
      (Blowup.Charts.Construction.blowupChartConstants (I.map (algebraMap R S)) (blowupBaseChangeElement I a) s)) = _
    rw [blowupChartToTensor_constants, blowupTensorToChart_right]
  · intro s
    rfl

/-- Flat base change of an actual blowup chart is its tensor product with
the new base ring. -/
def blowupChartFlatBaseChangeEquiv [Module.Flat R S] :
    blowupChartTensor (S := S) I a ≃+* blowupBaseChangedChart (S := S) I a :=
  RingEquiv.ofRingHom (blowupTensorToChart I a) (blowupChartToTensor I a)
    (blowupTensorToChart_chartToTensor I a) (blowupChartToTensor_tensorToChart I a)

/-- The coefficient-extension square of actual affine chart schemes is cartesian. -/
theorem blowupChart_flat_isPullback [Module.Flat R S] :
    IsPullback
      (Spec.map (CommRingCat.ofHom (ChartLift.Construction.blowupChartMap I (algebraMap R S) a)))
      (Spec.map (CommRingCat.ofHom (Blowup.Charts.Construction.blowupChartConstants (I.map (algebraMap R S))
        (blowupBaseChangeElement I a))))
      (Spec.map (CommRingCat.ofHom (Blowup.Charts.Construction.blowupChartConstants I a)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  apply isPullback_SpecMap_of_isPushout
  apply (CommRingCat.isPushout_tensorProduct R (Blowup.Charts.Construction.blowupChart I a) S).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (blowupChartFlatBaseChangeEquiv (S := S) I a).toCommRingCatIso
  · simp
  · simp
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact blowupTensorToChart_left I a x
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    exact blowupTensorToChart_right I a s

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ChartFlatBaseChange.Construction
