import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TransportModels

/-! # Cocycle -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Cocycle

noncomputable section

/-!
# The actual affine Čech cocycle implies the tensor descent cocycle
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Switch OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleGluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleExtension
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ThirdModel OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Transport OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TransportModels

/-- A comparison after restricting scalars is the same equality on underlying elements. -/
theorem restrict_comparison_apply {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) {X Y : ModuleCat.{u} B} {Z : ModuleCat.{u} A}
    (g : X ⟶ Y) (a : (restrictScalars f).obj X ⟶ Z)
    (b : (restrictScalars f).obj Y ⟶ Z) (t : Z ⟶ Z)
    (h : (restrictScalars f).map g ≫ b = a ≫ t) (x : X) :
    b (g x) = t (a x) :=
  ConcreteCategory.congr_hom h x

/-- A commutative module-morphism diagram gives its pointwise composition equation. -/
theorem module_comp_apply {A : Type u} [CommRing A] {X Y Z : ModuleCat.{u} A}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) (x : X) :
    g (f x) = k x :=
  ConcreteCategory.congr_hom h x

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (M : ModuleCat.{u} S)

/-- Interchange the two coefficient factors in the common tensor model. -/
def coefficientSwap : TripleExtension.tripleModule R S M ≃ₗ[R] TripleExtension.tripleModule R S M :=
  TensorProduct.leftComm R S S ((restrictScalars (algebraMap R S)).obj M)

theorem coefficientSwap_involutive (z : TripleExtension.tripleModule R S M) :
    coefficientSwap R S M (coefficientSwap R S M z) = z := by
  have h : (coefficientSwap R S M).toLinearMap ∘ₗ (coefficientSwap R S M).toLinearMap =
      LinearMap.id := TensorProduct.ext_threefold' (fun _ _ _ => rfl)
  exact LinearMap.congr_fun h z

/-- Pointwise form of the first-to-second gluing comparison. -/
theorem gluing12_model_apply (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M)
    (z : TripleGluing.slotModule R S M (TripleGluing.slot1 R S)) :
    (TripleGluing.secondFlatModel R S M).hom (TripleGluing.gluing12 R S M σ z) =
      TripleExtension.tripleSwitch R S M σ ((TripleGluing.firstFlatModel R S M).hom z) :=
  restrict_comparison_apply (TripleGluing.slot3 R S) (TripleGluing.gluing12 R S M σ)
    (TripleGluing.firstFlatModel R S M).hom (TripleGluing.secondFlatModel R S M).hom (TripleExtension.tripleSwitch R S M σ)
    (TripleGluing.gluing12_model R S M σ) z

/-- First-to-third gluing is the tensor switch after interchanging the coefficient factors. -/
theorem gluing13_model_apply (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M)
    (z : TripleGluing.slotModule R S M (TripleGluing.slot1 R S)) :
    ThirdModel.thirdFlatModel R S M (TripleGluing.gluing13 R S M σ z) =
      TripleExtension.tripleSwitch R S M σ (coefficientSwap R S M ((TripleGluing.firstFlatModel R S M).hom z)) := by
  obtain ⟨w, rfl⟩ := (Transport.swap23OnFirst R S M).surjective z
  have hs : coefficientSwap R S M
      ((TripleGluing.firstFlatModel R S M).hom (Transport.swap23OnFirst R S M w)) =
        (TripleGluing.firstFlatModel R S M).hom w :=
    (congrArg (coefficientSwap R S M) (TransportModels.firstModel_swap23 R S M w)).trans
      (coefficientSwap_involutive R S M _)
  calc
    _ = ThirdModel.thirdFlatModel R S M (Transport.swap23OnSecond R S M (TripleGluing.gluing12 R S M σ w)) :=
      congrArg (ThirdModel.thirdFlatModel R S M) (Transport.transport_gluing12 R S M σ w).symm
    _ = (TripleGluing.secondFlatModel R S M).hom (TripleGluing.gluing12 R S M σ w) := TransportModels.thirdModel_swap23 R S M _
    _ = TripleExtension.tripleSwitch R S M σ ((TripleGluing.firstFlatModel R S M).hom w) := gluing12_model_apply R S M σ w
    _ = _ := congrArg (TripleExtension.tripleSwitch R S M σ) hs.symm

/-- Second-to-third gluing is conjugated by interchange of the coefficient factors. -/
theorem gluing23_model_apply (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M)
    (z : TripleGluing.slotModule R S M (TripleGluing.slot2 R S)) :
    ThirdModel.thirdFlatModel R S M (TripleGluing.gluing23 R S M σ z) =
      coefficientSwap R S M (TripleExtension.tripleSwitch R S M σ
        (coefficientSwap R S M ((TripleGluing.secondFlatModel R S M).hom z))) := by
  obtain ⟨w, rfl⟩ := (Transport.swap12OnFirst R S M).surjective z
  calc
    _ = ThirdModel.thirdFlatModel R S M (Transport.swap12OnThird R S M (TripleGluing.gluing13 R S M σ w)) :=
      congrArg (ThirdModel.thirdFlatModel R S M) (Transport.transport_gluing13 R S M σ w).symm
    _ = coefficientSwap R S M (ThirdModel.thirdFlatModel R S M (TripleGluing.gluing13 R S M σ w)) :=
      TransportModels.thirdModel_swap12 R S M _
    _ = coefficientSwap R S M (TripleExtension.tripleSwitch R S M σ
        (coefficientSwap R S M ((TripleGluing.firstFlatModel R S M).hom w))) :=
      congrArg (coefficientSwap R S M) (gluing13_model_apply R S M σ w)
    _ = _ := congrArg (fun x => coefficientSwap R S M
      (TripleExtension.tripleSwitch R S M σ (coefficientSwap R S M x))) (TransportModels.secondModel_swap12 R S M w).symm

/-- The native three-gluing-map equation implies the switch cocycle pointwise. -/
theorem gluingSwitch_cocycle_apply (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M)
    (h : TripleGluing.gluing12 R S M σ ≫ TripleGluing.gluing23 R S M σ = TripleGluing.gluing13 R S M σ)
    (x : TripleExtension.tripleModule R S M) :
    TripleExtension.tripleSwitch R S M σ (coefficientSwap R S M (TripleExtension.tripleSwitch R S M σ x)) =
      coefficientSwap R S M (TripleExtension.tripleSwitch R S M σ (coefficientSwap R S M x)) := by
  obtain ⟨w, rfl⟩ := (TripleGluing.firstFlatModel R S M).toLinearEquiv.surjective x
  have hh := congrArg (ThirdModel.thirdFlatModel R S M)
    (module_comp_apply (TripleGluing.gluing12 R S M σ) (TripleGluing.gluing23 R S M σ) (TripleGluing.gluing13 R S M σ) h w)
  have hm : coefficientSwap R S M (TripleExtension.tripleSwitch R S M σ (coefficientSwap R S M
        (TripleExtension.tripleSwitch R S M σ ((TripleGluing.firstFlatModel R S M).hom w)))) =
      TripleExtension.tripleSwitch R S M σ (coefficientSwap R S M ((TripleGluing.firstFlatModel R S M).hom w)) := by
    calc
      _ = coefficientSwap R S M (TripleExtension.tripleSwitch R S M σ (coefficientSwap R S M
          ((TripleGluing.secondFlatModel R S M).hom (TripleGluing.gluing12 R S M σ w)))) :=
        congrArg (fun y => coefficientSwap R S M
          (TripleExtension.tripleSwitch R S M σ (coefficientSwap R S M y))) (gluing12_model_apply R S M σ w).symm
      _ = ThirdModel.thirdFlatModel R S M (TripleGluing.gluing23 R S M σ (TripleGluing.gluing12 R S M σ w)) :=
        (gluing23_model_apply R S M σ _).symm
      _ = ThirdModel.thirdFlatModel R S M (TripleGluing.gluing13 R S M σ w) := hh
      _ = _ := gluing13_model_apply R S M σ w
  exact (coefficientSwap_involutive R S M _).symm.trans
    (congrArg (coefficientSwap R S M) hm)

/-- The actual affine Čech cocycle gives the three-factor identity for the tensor switch. -/
theorem gluingSwitch_cocycle (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M)
    (h : TripleGluing.gluing12 R S M σ ≫ TripleGluing.gluing23 R S M σ = TripleGluing.gluing13 R S M σ) :
    DescentSwitch.nextSwitch R S ((restrictScalars (algebraMap R S)).obj M)
        (Switch.gluingSwitch R S M σ) ∘ₗ (coefficientSwap R S M).toLinearMap ∘ₗ
      DescentSwitch.nextSwitch R S ((restrictScalars (algebraMap R S)).obj M)
        (Switch.gluingSwitch R S M σ) =
    (coefficientSwap R S M).toLinearMap ∘ₗ
      DescentSwitch.nextSwitch R S ((restrictScalars (algebraMap R S)).obj M)
        (Switch.gluingSwitch R S M σ) ∘ₗ (coefficientSwap R S M).toLinearMap := by
  apply LinearMap.ext
  intro x
  exact gluingSwitch_cocycle_apply R S M σ h x

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Cocycle
