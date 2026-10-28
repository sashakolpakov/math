import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedParameters
import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraEquivRegularSequence
import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraEquivDifferentialBasis

/-! # Pointed Parameter Geometry -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedParameterGeometry

noncomputable section

/-! The actual pointed frame parameter map preserves weak regularity
and transports the matching basis of differentials. -/
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

local instance sourceAlgebra₁ :
    Algebra (Truncated.Witt.Ring p k n) Γ(X₁.left, U₁.val) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (Truncated.Witt.Ring p k n) X₁ U₁.val
local instance sourceAlgebra₂ :
    Algebra (Truncated.Witt.Ring p k n) Γ(X₂.left, U₂.val) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (Truncated.Witt.Ring p k n) X₂ U₂.val

variable
  (s₁ : Spec (CommRingCat.of (Truncated.Witt.Ring p k n)) ⟶ X₁.left)
  (hs₁ : s₁ ≫ X₁.hom = 𝟙 _)
  (s₂ : Spec (CommRingCat.of (Truncated.Witt.Ring p k n)) ⟶ X₂.left)
  (hs₂ : s₂ ≫ X₂.hom = 𝟙 _)
  (s₀ : Spec (CommRingCat.of k) ⟶ Y.left) (hs₀ : s₀ ≫ Y.hom = 𝟙 _)
  (hred₁ : s₀ ≫ f₁ = Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n)) ≫ s₁)
  (hred₂ : s₀ ≫ f₂ = Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n)) ≫ s₂)
  (h₁ : ⊤ ≤ s₁ ⁻¹ᵁ U₁.val) (h₂ : ⊤ ≤ s₂ ⁻¹ᵁ U₂.val)
  (g : ℕ) (b : Fin g → Γ(X₁.left, U₁.val))

theorem regular (hb : RingTheory.Sequence.IsWeaklyRegular Γ(X₁.left, U₁.val) (List.ofFn b)) :
    RingTheory.Sequence.IsWeaklyRegular Γ(X₂.left, U₂.val)
      (List.ofFn (PointedParameters.parameters
        p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ g b)) :=
  AlgebraEquivRegularSequence.regular
    (PointedLocalEquiv.equiv
      p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂).toRingEquiv b hb

def basis (d : Module.Basis (Fin g) Γ(X₁.left, U₁.val)
    Ω[Γ(X₁.left, U₁.val)⁄(Truncated.Witt.Ring p k n)]) :
    Module.Basis (Fin g) Γ(X₂.left, U₂.val)
      Ω[Γ(X₂.left, U₂.val)⁄(Truncated.Witt.Ring p k n)] :=
  AlgebraEquivDifferentialBasis.basis
    (PointedLocalEquiv.equiv
      p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂) d

theorem basis_apply (d : Module.Basis (Fin g) Γ(X₁.left, U₁.val)
    Ω[Γ(X₁.left, U₁.val)⁄(Truncated.Witt.Ring p k n)])
    (hd : ∀ j, d j = KaehlerDifferential.D (Truncated.Witt.Ring p k n) Γ(X₁.left, U₁.val) (b j))
    (j : Fin g) :
    basis p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ g d j =
      KaehlerDifferential.D (Truncated.Witt.Ring p k n) Γ(X₂.left, U₂.val)
        (PointedParameters.parameters
          p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ g b j) :=
  AlgebraEquivDifferentialBasis.basis_apply
    (PointedLocalEquiv.equiv
      p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂) d b hd j

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedParameterGeometry
