import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.NilCommonReduction

/-! # Local Equiv -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalEquiv

noncomputable section

/-! Two genuine affine smooth models of the same special open admit
an algebra isomorphism inducing the specified identity on that open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ)
  (X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [Smooth X₁.hom] [Smooth X₂.hom]
  (Y : Over (Spec (CommRingCat.of k)))
  (f₁ : Y.left ⟶ X₁.left) (f₂ : Y.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y.hom X₂.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U₁ : X₁.left.affineOpens) (U₂ : X₂.left.affineOpens)
  (h : f₁ ⁻¹ᵁ U₁.val = f₂ ⁻¹ᵁ U₂.val)

local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.sourceRing p k n X₁ U₁.val
local notation "B" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.sourceRing p k n X₂ U₂.val
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.targetRing p k n X₁ Y f₁ U₁.val
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.targetRing p k n X₂ Y f₂ U₂.val
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalIso.residueEquiv p k n X₁ X₂ Y f₁ f₂ U₁ U₂ h

local instance sourceAlgebra₁ : Algebra S A := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X₁ U₁.val
local instance sourceAlgebra₂ : Algebra S B := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X₂ U₂.val
local instance residueAlgebra₁ : Algebra k C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k Y _
local instance residueAlgebra₂ : Algebra k D := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k Y _
local instance residueBase : Algebra S k := (Truncated.Witt.reduction p k n).toAlgebra
local instance commonBase : Algebra S D :=
  AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.ReductionRing.BaseAffineReductionRing.targetAlgebra S k X₂ Y f₂ U₂.val
local instance sourceSmooth₁ : Algebra.Smooth S A :=
  Truncated.AffineModelFrame.source_smooth p k n X₁ U₁.val U₁.property
local instance sourceSmooth₂ : Algebra.Smooth S B :=
  Truncated.AffineModelFrame.source_smooth p k n X₂ U₂.val U₂.property

def leftReduction : A →ₐ[S] D where
  __ := (e).toRingHom.comp (f₁.app U₁.val).hom
  commutes' r := by
    change e ((f₁.app U₁.val).hom (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap S X₁ U₁.val r)) =
      algebraMap k D (Truncated.Witt.reduction p k n r)
    rw [AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.ReductionRing.BaseAffineReductionRing.base S k X₁ Y f₁ hp₁ U₁.val U₁.property]
    exact (e).commutes _

def rightReduction : B →ₐ[S] D where
  __ := (f₂.app U₂.val).hom
  commutes' r := AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.ReductionRing.BaseAffineReductionRing.base S k X₂ Y f₂ hp₂ U₂.val U₂.property r

omit [Smooth X₁.hom] [Smooth X₂.hom] in
theorem left_surjective : Function.Surjective (leftReduction p k n X₁ X₂ Y f₁ f₂ hp₁ U₁ U₂ h) :=
  (e).surjective.comp
    (Truncated.AffineModelFrame.reduction_surjective p k n X₁ Y f₁ hp₁ U₁.val U₁.property)

omit [Smooth X₁.hom] [Smooth X₂.hom] in
theorem right_surjective : Function.Surjective (rightReduction p k n X₂ Y f₂ hp₂ U₂) :=
  Truncated.AffineModelFrame.reduction_surjective p k n X₂ Y f₂ hp₂ U₂.val U₂.property

omit [Smooth X₁.hom] [Smooth X₂.hom] in
theorem left_kernel :
    RingHom.ker (leftReduction p k n X₁ X₂ Y f₁ f₂ hp₁ U₁ U₂ h).toRingHom =
      (Ideal.span {(p : S)}).map (algebraMap S A) := by
  change RingHom.ker ((e).toRingHom.comp (f₁.app U₁.val).hom) = _
  rw [RingHom.ker_equiv_comp]
  simpa only [Truncated.AffineModelFrame.reduction, Truncated.AffineModelFrame.sourceRing,
    Ideal.map_span, Set.image_singleton, map_natCast] using
    Truncated.AffineModelFrame.reduction_kernel p k n X₁ Y f₁ hp₁ U₁.val U₁.property

omit [Smooth X₂.hom] in
theorem right_kernel :
    RingHom.ker (rightReduction p k n X₂ Y f₂ hp₂ U₂).toRingHom =
      (Ideal.span {(p : S)}).map (algebraMap S B) := by
  simpa only [rightReduction, Truncated.AffineModelFrame.reduction,
    Ideal.map_span, Set.image_singleton, map_natCast] using
    Truncated.AffineModelFrame.reduction_kernel p k n X₂ Y f₂ hp₂ U₂.val U₂.property

omit [Fintype k] [CharP k p] in
theorem base_nilpotent : IsNilpotent (Ideal.span {(p : S)}) := by
  refine ⟨n + 1, ?_⟩
  exact (Ideal.span_singleton_pow (p : S) (n + 1)).trans
    ((congrArg (fun a : S => Ideal.span {a}) (Truncated.Witt.prime_power_zero p k n)).trans
      Ideal.span_singleton_zero)

def equiv : A ≃ₐ[S] B :=
  IntegralComparison.Smooth.NilCommonReduction.equiv (Ideal.span {(p : S)}) (base_nilpotent p k n)
    (leftReduction p k n X₁ X₂ Y f₁ f₂ hp₁ U₁ U₂ h)
    (left_surjective p k n X₁ X₂ Y f₁ f₂ hp₁ U₁ U₂ h)
    (left_kernel p k n X₁ X₂ Y f₁ f₂ hp₁ U₁ U₂ h)
    (rightReduction p k n X₂ Y f₂ hp₂ U₂)
    (right_surjective p k n X₂ Y f₂ hp₂ U₂)
    (right_kernel p k n X₂ Y f₂ hp₂ U₂)

theorem reduction_equiv (a : A) :
    (f₂.app U₂.val).hom (equiv p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h a) =
      LocalIso.Map.residueMap p k n X₁ X₂ Y f₁ f₂ U₁ U₂ h ((f₁.app U₁.val).hom a) :=
  IntegralComparison.Smooth.NilCommonReduction.reduction_equiv_apply (Ideal.span {(p : S)}) (base_nilpotent p k n)
    (leftReduction p k n X₁ X₂ Y f₁ f₂ hp₁ U₁ U₂ h)
    (left_surjective p k n X₁ X₂ Y f₁ f₂ hp₁ U₁ U₂ h)
    (left_kernel p k n X₁ X₂ Y f₁ f₂ hp₁ U₁ U₂ h)
    (rightReduction p k n X₂ Y f₂ hp₂ U₂)
    (right_surjective p k n X₂ Y f₂ hp₂ U₂)
    (right_kernel p k n X₂ Y f₂ hp₂ U₂) a

def frameIso := LocalIso.iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h
  (equiv p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h)
  (reduction_equiv p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalEquiv
