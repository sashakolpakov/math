import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrameMorphism

/-! # Local Iso -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalIso.Map

/-! A map between actual affine model section algebras, normalized on a
common special open, gives the original bounded and small frame maps. -/
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
local instance sourceAlgebra₁ : Algebra S A := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X₁ U₁.val
local instance sourceAlgebra₂ : Algebra S B := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X₂ U₂.val
local instance residueAlgebra₁ : Algebra k C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k Y _
local instance residueAlgebra₂ : Algebra k D := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k Y _
local instance sourceSmooth₁ : Algebra.Smooth S A :=
  Truncated.AffineModelFrame.source_smooth p k n X₁ U₁.val U₁.property
local instance sourceSmooth₂ : Algebra.Smooth S B :=
  Truncated.AffineModelFrame.source_smooth p k n X₂ U₂.val U₂.property

def residueMap : C →ₐ[k] D :=
  ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k Y).map (eqToHom h.symm).op).hom

omit [Smooth X₁.hom] [Smooth X₂.hom] in
theorem residueMap_chart : Spec.map (CommRingCat.ofHom (residueMap p k n X₁ X₂ Y f₁ f₂ U₁ U₂ h).toRingHom) ≫
    Truncated.AffineModelFrame.chart p k n X₁ Y f₁ hp₁ U₁.val U₁.property =
      Truncated.AffineModelFrame.chart p k n X₂ Y f₂ hp₂ U₂.val U₂.property :=
  (Truncated.AffineModelFrame.residue_affine p k n X₁ Y f₁ hp₁ U₁.val U₁.property).map_fromSpec
    (Truncated.AffineModelFrame.residue_affine p k n X₂ Y f₂ hp₂ U₂.val U₂.property)
    (eqToHom h.symm).op

variable (φ : Γ(X₁.left, U₁.val) →ₐ[Truncated.Witt.Ring p k n] Γ(X₂.left, U₂.val))
  (hφ : ∀ a, (f₂.app U₂.val).hom (φ a) =
    residueMap p k n X₁ X₂ Y f₁ f₂ U₁ U₂ h ((f₁.app U₁.val).hom a))

local notation "F₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.frame p k n X₁ Y f₁ hp₁ U₁.val U₁.property
local notation "F₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.frame p k n X₂ Y f₂ hp₂ U₂.val U₂.property

include φ hφ in
theorem overX : Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap
    (F₂).obj (F₁).obj (Truncated.SmoothFrameMorphism.dpMap p k n A B φ))) ≫ (F₁).obj.mapToX =
      (F₂).obj.mapToX := by
  have hx := (Truncated.SmoothFrameMorphism.morphism p k n A B φ C D
    (Truncated.AffineModelFrame.reduction p k n X₁ Y f₁ U₁.val)
    (Truncated.AffineModelFrame.reduction_surjective p k n X₁ Y f₁ hp₁ U₁.val U₁.property)
    (Truncated.AffineModelFrame.reduction_kernel p k n X₁ Y f₁ hp₁ U₁.val U₁.property)
    (Truncated.AffineModelFrame.reduction_base p k n X₁ Y f₁ hp₁ U₁.val U₁.property)
    (Truncated.AffineModelFrame.reduction p k n X₂ Y f₂ U₂.val)
    (Truncated.AffineModelFrame.reduction_surjective p k n X₂ Y f₂ hp₂ U₂.val U₂.property)
    (Truncated.AffineModelFrame.reduction_kernel p k n X₂ Y f₂ hp₂ U₂.val U₂.property)
    (Truncated.AffineModelFrame.reduction_base p k n X₂ Y f₂ hp₂ U₂.val U₂.property)
    (residueMap p k n X₁ X₂ Y f₁ f₂ U₁ U₂ h) hφ).overX
  have ht := congrArg (fun t => t ≫ Truncated.AffineModelFrame.chart p k n X₁ Y f₁ hp₁ U₁.val U₁.property) hx
  change (_ ≫ _) ≫ _ = (_ ≫ _) ≫ _ at ht
  rw [Category.assoc, Category.assoc, residueMap_chart] at ht
  exact ht

def boundedMap : F₂ ⟶ F₁ := ObjectProperty.homMk
  { ringMap := Truncated.SmoothFrameMorphism.dpMap p k n A B φ
    overBase := Truncated.SmoothFrameMorphism.overBase p k n A B φ
    overX := Map.overX p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h φ hφ }

def smallMap : (SmallFrame.smallFunctor p k n X₂ Y f₂ hp₂).obj U₂ ⟶
    (SmallFrame.smallFunctor p k n X₁ Y f₁ hp₁).obj U₁ where
  ringMap := Truncated.SmoothFrameMorphism.dpMap p k n A B φ
  overBase := Truncated.SmoothFrameMorphism.overBase p k n A B φ
  overX := Map.overX p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h φ hφ

def map : (SmallFrame.functor p k n X₂ Y f₂ hp₂).obj U₂ ⟶
    (SmallFrame.functor p k n X₁ Y f₁ hp₁).obj U₁ :=
  GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.to62.map (smallMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h φ hφ)

theorem map_ambient (a : A) : (Map.map p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h φ hφ).ambientMap a = φ a := rfl

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalIso.Map

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalIso

/-! A reduction-normalized affine algebra isomorphism induces isomorphisms
of the two original truncated-model frames over the common special open. -/
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
local instance sourceAlgebra₁ : Algebra S A := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X₁ U₁.val
local instance sourceAlgebra₂ : Algebra S B := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X₂ U₂.val
local instance residueAlgebra₁ : Algebra k C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k Y _
local instance residueAlgebra₂ : Algebra k D := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k Y _

def residueEquiv : C ≃ₐ[k] D :=
  CommAlgCat.algEquivOfIso ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k Y).mapIso (eqToIso h.symm).op)

omit [Fintype k] [CharP k p] [Smooth X₁.hom] [Smooth X₂.hom] in
theorem residueEquiv_apply (c : C) : residueEquiv p k n X₁ X₂ Y f₁ f₂ U₁ U₂ h c =
    Map.residueMap p k n X₁ X₂ Y f₁ f₂ U₁ U₂ h c := rfl

omit [Fintype k] [CharP k p] [Smooth X₁.hom] [Smooth X₂.hom] in
theorem residueEquiv_symm_apply (d : D) : (residueEquiv p k n X₁ X₂ Y f₁ f₂ U₁ U₂ h).symm d =
    Map.residueMap p k n X₂ X₁ Y f₂ f₁ U₂ U₁ h.symm d := rfl

variable (e : Γ(X₁.left, U₁.val) ≃ₐ[Truncated.Witt.Ring p k n] Γ(X₂.left, U₂.val))
  (he : ∀ a, (f₂.app U₂.val).hom (e a) =
    Map.residueMap p k n X₁ X₂ Y f₁ f₂ U₁ U₂ h ((f₁.app U₁.val).hom a))

omit [Fintype k] [CharP k p] [Smooth X₁.hom] [Smooth X₂.hom] in
include e he in
theorem inverse_reduction (b : B) : (f₁.app U₁.val).hom (e.symm b) =
    Map.residueMap p k n X₂ X₁ Y f₂ f₁ U₂ U₁ h.symm ((f₂.app U₂.val).hom b) := by
  have hh := he (e.symm b)
  rw [e.apply_symm_apply] at hh
  have ht := congrArg (residueEquiv p k n X₁ X₂ Y f₁ f₂ U₁ U₂ h).symm hh
  change (residueEquiv p k n X₁ X₂ Y f₁ f₂ U₁ U₂ h).symm ((f₂.app U₂.val).hom b) =
    (residueEquiv p k n X₁ X₂ Y f₁ f₂ U₁ U₂ h).symm
      (residueEquiv p k n X₁ X₂ Y f₁ f₂ U₁ U₂ h ((f₁.app U₁.val).hom (e.symm b))) at ht
  rw [AlgEquiv.symm_apply_apply] at ht
  exact ht.symm

def boundedIso :
    Truncated.AffineModelFrame.frame p k n X₂ Y f₂ hp₂ U₂.val U₂.property ≅
      Truncated.AffineModelFrame.frame p k n X₁ Y f₁ hp₁ U₁.val U₁.property where
  hom := Map.boundedMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h e.toAlgHom he
  inv := Map.boundedMap p k n X₂ X₁ Y f₂ f₁ hp₂ hp₁ U₂ U₁ h.symm e.symm.toAlgHom
    (inverse_reduction p k n X₁ X₂ Y f₁ f₂ U₁ U₂ h e he)
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply BigCrystallineSite.Object.Hom.ext
    ext b
    exact e.apply_symm_apply b
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply BigCrystallineSite.Object.Hom.ext
    ext a
    exact e.symm_apply_apply a

def smallIso : (SmallFrame.smallFunctor p k n X₂ Y f₂ hp₂).obj U₂ ≅
    (SmallFrame.smallFunctor p k n X₁ Y f₁ hp₁).obj U₁ where
  hom := Map.smallMap p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h e.toAlgHom he
  inv := Map.smallMap p k n X₂ X₁ Y f₂ f₁ hp₂ hp₁ U₂ U₁ h.symm e.symm.toAlgHom
    (inverse_reduction p k n X₁ X₂ Y f₁ f₂ U₁ U₂ h e he)
  hom_inv_id := by
    apply Crystalline.Site.AffineThickening.Hom.ext
    ext b
    exact e.apply_symm_apply b
  inv_hom_id := by
    apply Crystalline.Site.AffineThickening.Hom.ext
    ext a
    exact e.symm_apply_apply a

def iso : (SmallFrame.functor p k n X₂ Y f₂ hp₂).obj U₂ ≅
    (SmallFrame.functor p k n X₁ Y f₁ hp₁).obj U₁ :=
  GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.to62.mapIso (smallIso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h e he)

theorem iso_hom_ambient (a : A) : (iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h e he).hom.ambientMap a = e a := rfl

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalIso

end

end OAI
