import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedLocalEquiv
import OAI.NumberTheory.PadicHodge.IntegralComparison.PointedParameterTransport

/-! # Pointed Parameters -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedParameters

noncomputable section

/-! The actual pointed frame isomorphism transports generators of the section ideal. -/

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

local instance sourceAlgebra₁ : Algebra S A := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X₁ U₁.val
local instance sourceAlgebra₂ : Algebra S B := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X₂ U₂.val

variable
  (s₁ : Spec (CommRingCat.of (Truncated.Witt.Ring p k n)) ⟶ X₁.left)
  (hs₁ : s₁ ≫ X₁.hom = 𝟙 _)
  (s₂ : Spec (CommRingCat.of (Truncated.Witt.Ring p k n)) ⟶ X₂.left)
  (hs₂ : s₂ ≫ X₂.hom = 𝟙 _)
  (s₀ : Spec (CommRingCat.of k) ⟶ Y.left) (hs₀ : s₀ ≫ Y.hom = 𝟙 _)
  (hred₁ : s₀ ≫ f₁ = Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n)) ≫ s₁)
  (hred₂ : s₀ ≫ f₂ = Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n)) ≫ s₂)
  (h₁ : ⊤ ≤ s₁ ⁻¹ᵁ U₁.val) (h₂ : ⊤ ≤ s₂ ⁻¹ᵁ U₂.val)

local notation "εA" => OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionEvaluation.evaluation S X₁ s₁ hs₁ U₁.val h₁
local notation "εB" => OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionEvaluation.evaluation S X₂ s₂ hs₂ U₂.val h₂
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedLocalEquiv.equiv
  p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂

variable [IsClosedImmersion s₁] [IsClosedImmersion s₂]
  (g : ℕ) (b : Fin g → Γ(X₁.left, U₁.val))

def parameters : Fin g → Γ(X₂.left, U₂.val) := fun i =>
  (PointedLocalEquiv.frameIso
    p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂).hom.ambientMap (b i)

theorem span (hb : Ideal.span (Set.range b) = s₁.ker.ideal U₁) :
    Ideal.span (Set.range (parameters
      p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ g b)) =
        s₂.ker.ideal U₂ := by
  have ha : Ideal.span (Set.range b) = RingHom.ker (εA).toRingHom :=
    hb.trans (Intrinsic.SectionEvaluation.kernel S X₁ s₁ hs₁ U₁.val h₁ U₁.property).symm
  exact (PointedParameterTransport.span e εA εB
    (PointedLocalEquiv.section_equiv
      p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂) b ha).trans
    (Intrinsic.SectionEvaluation.kernel S X₂ s₂ hs₂ U₂.val h₂ U₂.property)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedParameters
