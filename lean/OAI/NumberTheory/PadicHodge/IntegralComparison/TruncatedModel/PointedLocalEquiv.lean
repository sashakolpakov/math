import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalEquiv
import OAI.NumberTheory.PadicHodge.IntegralComparison.PointedSmoothCommonResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionPointedCoordinates

/-! # Pointed Local Equiv -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedLocalEquiv

noncomputable section

/-! Genuine affine smooth models of the same special open admit an
isomorphism preserving both that open and the original point sections. -/

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

local instance commonTower : IsScalarTower S k D :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

variable
  (s₁ : Spec (CommRingCat.of (Truncated.Witt.Ring p k n)) ⟶ X₁.left)
  (hs₁ : s₁ ≫ X₁.hom = 𝟙 _)
  (s₂ : Spec (CommRingCat.of (Truncated.Witt.Ring p k n)) ⟶ X₂.left)
  (hs₂ : s₂ ≫ X₂.hom = 𝟙 _)
  (s₀ : Spec (CommRingCat.of k) ⟶ Y.left) (hs₀ : s₀ ≫ Y.hom = 𝟙 _)
  (hred₁ : s₀ ≫ f₁ = Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n)) ≫ s₁)
  (hred₂ : s₀ ≫ f₂ = Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n)) ≫ s₂)
  (h₁ : ⊤ ≤ s₁ ⁻¹ᵁ U₁.val) (h₂ : ⊤ ≤ s₂ ⁻¹ᵁ U₂.val)

local notation "πA" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalEquiv.leftReduction p k n X₁ X₂ Y f₁ f₂ hp₁ U₁ U₂ h
local notation "πB" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalEquiv.rightReduction p k n X₂ Y f₂ hp₂ U₂
local notation "εA" => OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionEvaluation.evaluation S X₁ s₁ hs₁ U₁.val h₁
local notation "εB" => OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionEvaluation.evaluation S X₂ s₂ hs₂ U₂.val h₂
local notation "h₀₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionPointedCoordinates.contains
  (Truncated.Witt.reduction p k n) X₁ Y f₁ s₁ s₀ hred₁ U₁.val h₁
local notation "h₀₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionPointedCoordinates.contains
  (Truncated.Witt.reduction p k n) X₂ Y f₂ s₂ s₀ hred₂ U₂.val h₂

def baseMap : S →ₐ[S] k := Algebra.ofId S k

theorem base_kernel : RingHom.ker (baseMap p k n).toRingHom = Ideal.span {(p : S)} := by
  change RingHom.ker (Truncated.Witt.reduction p k n) = _
  rw [Truncated.Witt.reduction_kernel]
  change (Ideal.span {(p : WittVector p k)}).map (Truncated.Witt.quotient p k n) = _
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

def commonEvaluation : D →ₐ[S] k := by
  let ε : D →ₐ[k] k :=
    Intrinsic.SectionEvaluation.evaluation k Y s₀ hs₀ (f₂ ⁻¹ᵁ U₂.val) h₀₂
  exact ε.restrictScalars S

local notation "εC" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedLocalEquiv.commonEvaluation p k n X₂ Y f₂ U₂ s₂ s₀ hs₀ hred₂ h₂

include hred₁ in
omit [Smooth X₁.hom] [Smooth X₂.hom] in
theorem left_compatibility : (εC).comp πA = (baseMap p k n).comp εA := by
  apply AlgHom.ext
  intro a
  have ht := Intrinsic.SectionPointedCoordinates.IntrinsicEvaluation.transport k Y s₀ hs₀
    (f₁ ⁻¹ᵁ U₁.val) (f₂ ⁻¹ᵁ U₂.val) h h₀₁ h₀₂ (f₁.app U₁.val a)
  have hr := Intrinsic.SectionReductionEvaluation.evaluation (Truncated.Witt.reduction p k n)
    X₁ Y f₁ s₁ hs₁ s₀ hs₀ hred₁ U₁.val h₁ h₀₁ a
  exact ht.trans hr

omit [Smooth X₂.hom] in
theorem right_compatibility : (εC).comp πB = (baseMap p k n).comp εB := by
  apply AlgHom.ext
  intro a
  exact Intrinsic.SectionReductionEvaluation.evaluation (Truncated.Witt.reduction p k n)
    X₂ Y f₂ s₂ hs₂ s₀ hs₀ hred₂ U₂.val h₂ h₀₂ a

def equiv : A ≃ₐ[S] B :=
  PointedSmoothCommonResidue.equiv (Ideal.span {(p : S)}) (baseMap p k n)
    (Truncated.Witt.reduction_surjective p k n) (base_kernel p k n)
    εC πA εA (LocalEquiv.base_nilpotent p k n)
    (LocalEquiv.left_surjective p k n X₁ X₂ Y f₁ f₂ hp₁ U₁ U₂ h)
    (LocalEquiv.left_kernel p k n X₁ X₂ Y f₁ f₂ hp₁ U₁ U₂ h)
    πB (LocalEquiv.right_surjective p k n X₂ Y f₂ hp₂ U₂)
    (LocalEquiv.right_kernel p k n X₂ Y f₂ hp₂ U₂)
    εB (left_compatibility p k n X₁ X₂ Y f₁ f₂ hp₁ U₁ U₂ h s₁ hs₁ s₂ s₀ hs₀ hred₁ hred₂ h₁ h₂)
    (right_compatibility p k n X₂ Y f₂ hp₂ U₂ s₂ hs₂ s₀ hs₀ hred₂ h₂)

theorem reduction_equiv (a : A) :
    (f₂.app U₂.val).hom
      (equiv p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ a) =
    LocalIso.Map.residueMap p k n X₁ X₂ Y f₁ f₂ U₁ U₂ h ((f₁.app U₁.val).hom a) :=
  AlgHom.congr_fun (PointedSmoothCommonResidue.reduction_equiv
    (Ideal.span {(p : S)}) (baseMap p k n)
    (Truncated.Witt.reduction_surjective p k n) (base_kernel p k n)
    εC πA εA (LocalEquiv.base_nilpotent p k n)
    (LocalEquiv.left_surjective p k n X₁ X₂ Y f₁ f₂ hp₁ U₁ U₂ h)
    (LocalEquiv.left_kernel p k n X₁ X₂ Y f₁ f₂ hp₁ U₁ U₂ h)
    πB (LocalEquiv.right_surjective p k n X₂ Y f₂ hp₂ U₂)
    (LocalEquiv.right_kernel p k n X₂ Y f₂ hp₂ U₂)
    εB (left_compatibility p k n X₁ X₂ Y f₁ f₂ hp₁ U₁ U₂ h s₁ hs₁ s₂ s₀ hs₀ hred₁ hred₂ h₁ h₂)
    (right_compatibility p k n X₂ Y f₂ hp₂ U₂ s₂ hs₂ s₀ hs₀ hred₂ h₂)) a

theorem section_equiv (a : A) :
    εB (equiv p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ a) = εA a :=
  AlgHom.congr_fun (PointedSmoothCommonResidue.section_equiv
    (Ideal.span {(p : S)}) (baseMap p k n)
    (Truncated.Witt.reduction_surjective p k n) (base_kernel p k n)
    εC πA εA (LocalEquiv.base_nilpotent p k n)
    (LocalEquiv.left_surjective p k n X₁ X₂ Y f₁ f₂ hp₁ U₁ U₂ h)
    (LocalEquiv.left_kernel p k n X₁ X₂ Y f₁ f₂ hp₁ U₁ U₂ h)
    πB (LocalEquiv.right_surjective p k n X₂ Y f₂ hp₂ U₂)
    (LocalEquiv.right_kernel p k n X₂ Y f₂ hp₂ U₂)
    εB (left_compatibility p k n X₁ X₂ Y f₁ f₂ hp₁ U₁ U₂ h s₁ hs₁ s₂ s₀ hs₀ hred₁ hred₂ h₁ h₂)
    (right_compatibility p k n X₂ Y f₂ hp₂ U₂ s₂ hs₂ s₀ hs₀ hred₂ h₂)) a

def frameIso := LocalIso.iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h
  (equiv p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂)
  (reduction_equiv p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂)

theorem frameIso_section (a : A) :
    εB ((frameIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂).hom.ambientMap a) =
      εA a :=
  section_equiv p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedLocalEquiv
