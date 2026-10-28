import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedSquares
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.EquivCompatibility

/-! # Pointed Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedRestriction

noncomputable section

/-! Restrict the specified original pointed equivalence to a smaller
affine neighborhood and retain its native frame map and parameters. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem unrestricted_square {X₁ X₂ Y : Scheme}
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (U₁ : X₁.Opens) (U₂ : X₂.Opens)
    (h : f₁ ⁻¹ᵁ U₁ = f₂ ⁻¹ᵁ U₂) (φ : Γ(X₁, U₁) ⟶ Γ(X₂, U₂))
    (he : φ ≫ f₂.appLE U₂ (f₁ ⁻¹ᵁ U₁) h.le = f₁.app U₁) :
    φ ≫ f₂.app U₂ = f₁.app U₁ ≫ Y.presheaf.map (eqToHom h.symm).op := by
  have hh := congrArg (fun a => a ≫ Y.presheaf.map (eqToHom h.symm).op) he
  have hi : (homOfLE h.le).op ≫ (eqToHom h.symm).op = 𝟙 (op (f₂ ⁻¹ᵁ U₂)) :=
    Subsingleton.elim _ _
  simpa only [Scheme.Hom.appLE, Category.assoc, ← Functor.map_comp, hi,
    CategoryTheory.Functor.map_id, Category.comp_id] using hh

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
  (s₁ : Spec (CommRingCat.of (Truncated.Witt.Ring p k n)) ⟶ X₁.left)
  (hs₁ : s₁ ≫ X₁.hom = 𝟙 _)
  (s₂ : Spec (CommRingCat.of (Truncated.Witt.Ring p k n)) ⟶ X₂.left)
  (hs₂ : s₂ ≫ X₂.hom = 𝟙 _)
  (s₀ : Spec (CommRingCat.of k) ⟶ Y.left) (hs₀ : s₀ ≫ Y.hom = 𝟙 _)
  (hred₁ : s₀ ≫ f₁ = Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n)) ≫ s₁)
  (hred₂ : s₀ ≫ f₂ = Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n)) ≫ s₂)
  (h₁ : ⊤ ≤ s₁ ⁻¹ᵁ U₁.val) (h₂ : ⊤ ≤ s₂ ⁻¹ᵁ U₂.val)
  (V : X₁.left.affineOpens) (hVU : V.val ≤ U₁.val)

local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedLocalEquiv.equiv
  p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂

open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.EquivCompatibility.Geometry

def target : X₂.left.affineOpens :=
  ⟨AffineSection.EquivGeometry.targetOpen S X₁ X₂ U₁.val U₂.val U₁.property U₂.property e V.val,
    AffineSection.EquivGeometry.target_affine S X₁ X₂ U₁.val U₂.val U₁.property U₂.property e V.val V.property hVU⟩

local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedRestriction.target
  p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ V hVU

theorem target_le : (T).val ≤ U₂.val :=
  AffineSection.EquivGeometry.target_below S X₁ X₂ U₁.val U₂.val U₁.property U₂.property e V.val

def equiv := AffineSection.EquivGeometry.sectionEquiv S X₁ X₂ U₁.val U₂.val U₁.property U₂.property e V.val hVU

local notation "eV" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedRestriction.equiv
  p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ V hVU

theorem reduction : f₁ ⁻¹ᵁ V.val = f₂ ⁻¹ᵁ (T).val :=
  AffineSection.EquivReduction.Geometry.target_preimage S X₁ X₂ U₁.val U₂.val U₁.property U₂.property e f₁ f₂ h
    (PointedSquares.reduction_square
      p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂)
    V.val hVU

local notation "hVred" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedRestriction.reduction
  p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ V hVU

theorem reduction_square : CommRingCat.ofHom (eV).toRingHom ≫
    f₂.appLE (T).val (f₁ ⁻¹ᵁ V.val) (hVred).le = f₁.app V.val :=
  AffineSection.EquivCompatibility.Geometry.section_compatibility S X₁ X₂ U₁.val U₂.val U₁.property U₂.property e f₁ f₂ h
    (PointedSquares.reduction_square
      p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂)
    V.val V.property hVU

theorem reduction_equiv (a : Γ(X₁.left, V.val)) :
    (f₂.app (T).val).hom ((eV) a) =
      LocalIso.Map.residueMap p k n X₁ X₂ Y f₁ f₂ V T hVred ((f₁.app V.val).hom a) :=
  ConcreteCategory.congr_hom
    (unrestricted_square f₁ f₂ V.val (T).val hVred (CommRingCat.ofHom (eV).toRingHom)
      (reduction_square
        p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ V hVU)) a

def frameIso := LocalIso.iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ V T hVred eV
  (reduction_equiv
    p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ V hVU)

local notation "iV" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedRestriction.frameIso
  p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ V hVU

theorem frameIso_ambient (a : Γ(X₁.left, V.val)) : (iV).hom.ambientMap a = (eV) a := rfl

theorem restriction (a : Γ(X₁.left, U₁.val)) :
    (eV) (X₁.left.presheaf.map (homOfLE hVU).op a) =
      X₂.left.presheaf.map (homOfLE (target_le
        p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ V hVU)).op ((e) a) :=
  AffineSection.EquivRestriction.Geometry.sectionEquiv_restriction S X₁ X₂ U₁.val U₂.val U₁.property U₂.property e V.val hVU a

theorem frameIso_restriction (a : Γ(X₁.left, U₁.val)) :
    (iV).hom.ambientMap (X₁.left.presheaf.map (homOfLE hVU).op a) =
      X₂.left.presheaf.map (homOfLE (target_le
        p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ V hVU)).op
        ((PointedLocalEquiv.frameIso
          p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂).hom.ambientMap a) :=
  restriction
    p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ V hVU a

theorem section_preimage : s₁ ⁻¹ᵁ V.val = s₂ ⁻¹ᵁ (T).val :=
  AffineSection.EquivReduction.Geometry.target_preimage S X₁ X₂ U₁.val U₂.val U₁.property U₂.property e s₁ s₂
    ((top_unique h₁).trans (top_unique h₂).symm)
    (PointedSquares.section_square
      p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂)
    V.val hVU

theorem target_contains (hV : ⊤ ≤ s₁ ⁻¹ᵁ V.val) : ⊤ ≤ s₂ ⁻¹ᵁ (T).val := by
  rw [← section_preimage
    p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ V hVU]
  exact hV

theorem section_square : CommRingCat.ofHom (eV).toRingHom ≫
    s₂.appLE (T).val (s₁ ⁻¹ᵁ V.val)
      (section_preimage
        p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ V hVU).le = s₁.app V.val :=
  AffineSection.EquivCompatibility.Geometry.section_compatibility S X₁ X₂ U₁.val U₂.val U₁.property U₂.property e s₁ s₂
    ((top_unique h₁).trans (top_unique h₂).symm)
    (PointedSquares.section_square
      p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂)
    V.val V.property hVU

theorem section_equiv (hV : ⊤ ≤ s₁ ⁻¹ᵁ V.val) (a : Γ(X₁.left, V.val)) :
    Intrinsic.SectionEvaluation.evaluation S X₂ s₂ hs₂ (T).val
      (target_contains
        p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ V hVU hV) ((eV) a) =
    Intrinsic.SectionEvaluation.evaluation S X₁ s₁ hs₁ V.val hV a := by
  have hh := congrArg (fun m => m ≫
    (Spec (CommRingCat.of S)).presheaf.map (homOfLE hV).op)
    (section_square
      p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ V hVU)
  rw [Category.assoc, Scheme.Hom.appLE_map] at hh
  exact ConcreteCategory.congr_hom
    (congrArg (fun m => m ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom) hh) a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedRestriction
