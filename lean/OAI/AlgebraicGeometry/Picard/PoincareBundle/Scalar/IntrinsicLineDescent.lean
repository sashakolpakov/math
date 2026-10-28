import OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.KernelUnitValues
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.VerticalUnitDescent

/-! # Intrinsic Line Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.IntrinsicLineDescent.Intrinsic

noncomputable section

/-! Scalar-cover kernel descent of the pulled Poincare line is its canonical native line descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrameIsotropy OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.KernelDescent

private theorem point_property_congr {C : Type*} [Category C] {E B T : C} (f : E ⟶ B) (q : T ⟶ B)
    (P : ∀ x y : T ⟶ E, x ≫ f = q → y ≫ f = q → Prop)
    (x y x' y' : T ⟶ E) (hx : x ≫ f = q) (hy : y ≫ f = q)
    (hx' : x' ≫ f = q) (hy' : y' ≫ f = q) (ex : x = x') (ey : y = y')
    (h : P x y hx hy) : P x' y' hx' hy' := by
  subst x'
  subst y'
  exact h

variable {S : Scheme.{u}} {A Z : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj Z]
  (φ : A ⟶ Z) [IsMonHom φ] (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P) (n : ℕ)

omit [GrpObj Z] [IsMonHom φ] in
/-- The actual scalar-kernel translation is exactly the canonical pulled-line gluing morphism. -/
theorem hom_translation {T : Over S} (l : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n)) (z w : T ⟶ A) (x : T ⟶ A)
    (h : (l ≫ Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n)) * z = w) (q : T ⟶ A ⊗ A)
    (hz : lift x z ≫ (𝟙 A ⊗ₘ (𝟙 A) ^ n) = q) (hw : lift x w ≫ (𝟙 A ⊗ₘ (𝟙 A) ^ n) = q) :
    (Vertical.KernelDescent.nativeDatum ((𝟙 A) ^ n) ((FirstBiextensionFactor.familyLine P φ).pullback (𝟙 A ⊗ₘ (𝟙 A) ^ n).left)
      (Pulled.KernelFrameIsotropy.verticalMultiplication (𝟙 A) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv))
      (PullbackKernelFrames.frames φ P Dv n)).hom
      q.left (lift x z).left (lift x w).left (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw) =
    (Homomorphisms.LineKernelCocycle.Construction.pullbackLineNativeDatum (𝟙 A ⊗ₘ (𝟙 A) ^ n)
      (Line.Comparison.Bundle.toShared (FirstBiextensionFactor.familyLine P φ))).hom
      q.left (lift x z).left (lift x w).left (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw) := by
  have hd : lift x (l ≫ Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n)) ≫ (𝟙 A ⊗ₘ (𝟙 A) ^ n) = lift x 1 := by
    simp [Category.assoc, Kernel.Scheme.kernelInclusion_comp, MonObj.comp_one]
  exact Pulled.VerticalUnitDescent.hom_translation ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ)
    (Poincare.TransverseFrames.sourceVertical φ P Dv) (PullbackKernelFrames.frames φ P Dv n) l z w x h q hz hw hd
    (KernelUnitValues.frame_eq_to φ P Dv n l (lift x (l ≫ Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n)))
      (lift_snd _ _).symm (lift x 1) hd (lift_snd _ _))

omit [GrpObj Z] [IsMonHom φ] in
/-- All original-base test points have the same full gluing map in the two native descents. -/
theorem hom_eq {T : Over S} (q : T ⟶ A ⊗ A) (a b : T ⟶ A ⊗ A)
    (ha : a ≫ (𝟙 A ⊗ₘ (𝟙 A) ^ n) = q) (hb : b ≫ (𝟙 A ⊗ₘ (𝟙 A) ^ n) = q) :
    (Vertical.KernelDescent.nativeDatum ((𝟙 A) ^ n) ((FirstBiextensionFactor.familyLine P φ).pullback (𝟙 A ⊗ₘ (𝟙 A) ^ n).left)
      (Pulled.KernelFrameIsotropy.verticalMultiplication (𝟙 A) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv))
      (PullbackKernelFrames.frames φ P Dv n)).hom
      q.left a.left b.left (congrArg Over.Hom.left ha) (congrArg Over.Hom.left hb) =
    (Homomorphisms.LineKernelCocycle.Construction.pullbackLineNativeDatum (𝟙 A ⊗ₘ (𝟙 A) ^ n)
      (Line.Comparison.Bundle.toShared (FirstBiextensionFactor.familyLine P φ))).hom
      q.left a.left b.left (congrArg Over.Hom.left ha) (congrArg Over.Hom.left hb) := by
  have hr := Vertical.KernelDescent.relation ((𝟙 A) ^ n) a b (ha.trans hb.symm)
  let l := Kernel.Pair.pointDifference ((𝟙 A) ^ n) (a ≫ snd A A) (b ≫ snd A A) hr.1
  have h : (l ≫ Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n)) * (a ≫ snd A A) = b ≫ snd A A :=
    (mul_comm _ _).trans (Kernel.Linearization.difference_translates ((𝟙 A) ^ n)
      (a ≫ snd A A) (b ≫ snd A A) hr.1)
  have hea : lift (a ≫ fst A A) (a ≫ snd A A) = a := by cat_disch
  have heb : lift (a ≫ fst A A) (b ≫ snd A A) = b := by
    rw [hr.2]
    cat_disch
  have hla : lift (a ≫ fst A A) (a ≫ snd A A) ≫ (𝟙 A ⊗ₘ (𝟙 A) ^ n) = q :=
    (congrArg (fun v => v ≫ (𝟙 A ⊗ₘ (𝟙 A) ^ n)) hea).trans ha
  have hlb : lift (a ≫ fst A A) (b ≫ snd A A) ≫ (𝟙 A ⊗ₘ (𝟙 A) ^ n) = q :=
    (congrArg (fun v => v ≫ (𝟙 A ⊗ₘ (𝟙 A) ^ n)) heb).trans hb
  have he := hom_translation φ P Dv n l (a ≫ snd A A) (b ≫ snd A A) (a ≫ fst A A) h q hla hlb
  let R (a' b' : T ⟶ A ⊗ A) (ha' : a' ≫ (𝟙 A ⊗ₘ (𝟙 A) ^ n) = q)
      (hb' : b' ≫ (𝟙 A ⊗ₘ (𝟙 A) ^ n) = q) : Prop :=
    (Vertical.KernelDescent.nativeDatum ((𝟙 A) ^ n) ((FirstBiextensionFactor.familyLine P φ).pullback (𝟙 A ⊗ₘ (𝟙 A) ^ n).left)
      (Pulled.KernelFrameIsotropy.verticalMultiplication (𝟙 A) ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv))
      (PullbackKernelFrames.frames φ P Dv n)).hom
      q.left a'.left b'.left (congrArg Over.Hom.left ha') (congrArg Over.Hom.left hb') =
    (Homomorphisms.LineKernelCocycle.Construction.pullbackLineNativeDatum (𝟙 A ⊗ₘ (𝟙 A) ^ n)
      (Line.Comparison.Bundle.toShared (FirstBiextensionFactor.familyLine P φ))).hom
      q.left a'.left b'.left (congrArg Over.Hom.left ha') (congrArg Over.Hom.left hb')
  exact point_property_congr (𝟙 A ⊗ₘ (𝟙 A) ^ n) q R _ _ a b hla hlb ha hb hea heb he

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.IntrinsicLineDescent.Intrinsic
