import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Supported
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalPDNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IncomingSectionReindex

/-! # Frame Supported -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameSupported.Geometry

/-! Insert the original native frame geometry after the two comparison
squares have already been assembled on the bounded site. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ)
  (X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X₁.hom] [Smooth X₁.hom] [X₁.left.IsSeparated]
  [IsProper X₂.hom] [Smooth X₂.hom] [X₂.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom]
  (f₁ : Y.left ⟶ X₁.left) (f₂ : Y.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y.hom X₂.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U₁ : X₁.left.affineOpens) (U₂ : X₂.left.affineOpens)
  (e : (SmallFrame.functor p k n X₂ Y f₂ hp₂).obj U₂ ≅
    (SmallFrame.functor p k n X₁ Y f₁ hp₁).obj U₁)

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "O₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.opens p k n X₁ Y f₁ U₁
local notation "O₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSections.opens p k n X₂ Y f₂ U₂
local notation "G₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.frames p k n X₁ Y f₁ hp₁ U₁
local notation "G₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.frames p k n X₂ Y f₂ hp₂ U₂
local notation "F₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.center p k n X₁ Y f₁ hp₁ U₁
local notation "F₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.center p k n X₂ Y f₂ hp₂ U₂
local notation "ρ₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.cone p k n X₁ Y f₁ hp₁ U₁
local notation "ρ₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalIn.Family.cone p k n X₂ Y f₂ hp₂ U₂

attribute [local instance] LocalPrincipal.Sections.globalSeparated

abbrev comparison := by
  letI : IsIso (BoundedFrame.LocalMap.restriction w n (O₁).toFunctor.op G₁ F₁ ρ₁) :=
    PrincipalIn.Family.fixed_isIso p k n X₁ Y f₁ hp₁ U₁
  letI : IsIso (BoundedFrame.LocalMap.restriction w n (O₂).toFunctor.op G₂ F₂ ρ₂) :=
    PrincipalIn.Family.fixed_isIso p k n X₂ Y f₂ hp₂ U₂
  exact BoundedFrame.Supported.Comparison.comparison w n
    (PrincipalFamilyIso.Family.reindex p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
    O₁ O₂ G₁ G₂ F₁ F₂ ρ₁ ρ₂
    (PrincipalTransportedFamily.Family.iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
    (PrincipalTransportedFamily.Family.baseIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
    (PrincipalTransportedFamily.Family.projection_square p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
    (IncomingSectionReindex.family_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
    (PrincipalOpenFunctorEq.opens_eq p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).symm

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameSupported.Geometry

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameSupported.Coefficients

/-! Insert the original principal de Rham coefficients after the native
frame geometry, before choosing an injective resolution. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ)
  (X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X₁.hom] [Smooth X₁.hom] [X₁.left.IsSeparated]
  [IsProper X₂.hom] [Smooth X₂.hom] [X₂.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom]
  (f₁ : Y.left ⟶ X₁.left) (f₂ : Y.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y.hom X₂.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U₁ : X₁.left.affineOpens) (U₂ : X₂.left.affineOpens)
  (e : (SmallFrame.functor p k n X₂ Y f₂ hp₂).obj U₂ ≅
    (SmallFrame.functor p k n X₁ Y f₁ hp₁).obj U₁)

abbrev comparison := Geometry.comparison
  p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e
  (Principal.Comparison.source p k n X₁ Y f₁ hp₁ U₁)
  (Principal.Comparison.source p k n X₂ Y f₂ hp₂ U₂)
  (Principal.Comparison.coefficientMap p k n X₁ Y f₁ hp₁ U₁)
  (Principal.Comparison.coefficientMap p k n X₂ Y f₂ hp₂ U₂)
  (PrincipalCoefficientNaturality.sourceIso
    p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).hom
  (LocalPrincipal.PDNaturality.coefficient_square
    p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameSupported.Coefficients

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameSupported.Resolution

/-! Insert the original injective resolution and incoming comparison in
the assembled native bounded-frame square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ)
  (X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X₁.hom] [Smooth X₁.hom] [X₁.left.IsSeparated]
  [IsProper X₂.hom] [Smooth X₂.hom] [X₂.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom]
  (f₁ : Y.left ⟶ X₁.left) (f₂ : Y.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y.hom X₂.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U₁ : X₁.left.affineOpens) (U₂ : X₂.left.affineOpens)
  (e : (SmallFrame.functor p k n X₂ Y f₂ hp₂).obj U₂ ≅
    (SmallFrame.functor p k n X₁ Y f₁ hp₁).obj U₁)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

abbrev comparison := Coefficients.comparison
  p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e I
  (LocalIncomingHomotopy.preimage f₁ U₁)
  (LocalIncomingHomotopy.preimage f₂ U₂)
  (LocalIncomingHomotopy.opens_eq
    p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e)
  (PrincipalSections.le_chart p k n X₁ Y f₁ U₁)
  (PrincipalSections.le_chart p k n X₂ Y f₂ U₂)
  (IncomingFrame.comparison p k n X₂ Y f₂ hp₂ U₂ I)

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameSupported.Resolution

end

end OAI
