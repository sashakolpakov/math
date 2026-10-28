import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.PartialClass

/-! # Scalar Partial Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ScalarPartialClass

noncomputable section

/-! The complete supported partial-fraction class is linear in its
ordered top coefficient, with no choice of a functional representative. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorCoordinates
variable (R : Type u) [CommRing R] {c m : ℕ}

 theorem functional (φ : Module.Dual R (⋀[R]^(c+m) (KoszulPartial.Fractions.ambient R (c := c) (m := m)))) :
    φ = φ (TopExteriorCoordinates.generator (KoszulPartial.TopResidue.basis R)) •
      KoszulPartial.TopResidue.functional R := by
  apply LinearMap.ext
  intro x
  conv_lhs => rw [← TopExteriorCoordinates.reconstruct (KoszulPartial.TopResidue.basis R) x]
  rw [map_smul]
  change TopExteriorCoordinates.coordinate (KoszulPartial.TopResidue.basis R) x *
    φ (TopExteriorCoordinates.generator (KoszulPartial.TopResidue.basis R)) = _
  exact mul_comm _ _

 variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (P : Cᵒᵖ ⥤ CommAlgCat.{u} R) (U : ULift.{u} (Fin m) → C) (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

 theorem sourceClass_smul (a : R)
    (φ : Module.Dual R (⋀[R]^(c+m) (KoszulPartial.Fractions.ambient R (c := c) (m := m)))) :
    KoszulPartial.PartialClass.sourceClass R s t (a • φ) =
      a • KoszulPartial.PartialClass.sourceClass R s t φ := by
  change IntegralComparison.Module.CochainClasses.classMap _ _ _ = _
  have h : KoszulPartial.PartialClass.sourceCycle R s t (a • φ) =
      a • KoszulPartial.PartialClass.sourceCycle R s t φ := by
    apply Subtype.ext
    rfl
  rw [h, map_smul]
  rfl

 theorem supportedClass_smul (a : R)
    (φ : Module.Dual R (⋀[R]^(c+m) (KoszulPartial.Fractions.ambient R (c := c) (m := m)))) :
    KoszulPartial.PartialClass.supportedClass R P U s t ht (a • φ) =
      a • KoszulPartial.PartialClass.supportedClass R P U s t ht φ := by
  rw [KoszulPartial.PartialClass.supportedClass_eq, sourceClass_smul]
  exact ((homologyMap (KoszulPartial.Total.map R P U s t ht) (c+m)).hom.map_smul a _).trans
    (congrArg (fun x => a • x) (KoszulPartial.PartialClass.supportedClass_eq R P U s t ht φ).symm)

 theorem supportedClass_eq
    (φ : Module.Dual R (⋀[R]^(c+m) (KoszulPartial.Fractions.ambient R (c := c) (m := m)))) :
    KoszulPartial.PartialClass.supportedClass R P U s t ht φ =
      φ (TopExteriorCoordinates.generator (KoszulPartial.TopResidue.basis R)) •
        KoszulPartial.PartialClass.supportedClass R P U s t ht
          (KoszulPartial.TopResidue.functional R) :=
  (congrArg (KoszulPartial.PartialClass.supportedClass R P U s t ht) (functional R φ)).trans
    (supportedClass_smul R P U s t ht _ _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ScalarPartialClass
