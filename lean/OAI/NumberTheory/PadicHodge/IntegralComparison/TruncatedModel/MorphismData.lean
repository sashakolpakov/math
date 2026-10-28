import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.OpenSectionGeometricPullback

/-! # Morphism Data -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData

/-! A morphism of actual finite-level models gives compatible section
maps and the prescribed geometric square on every affine refinement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [Smooth X₁.hom] [Smooth X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)
  (U : X₂.left.Opens) (V : X₁.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
  (hu : V ≤ u.left ⁻¹ᵁ U)

local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.sourceRing p k n X₂ U
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.sourceRing p k n X₁ V
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.targetRing p k n X₂ Y₂ f₂ U
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.targetRing p k n X₁ Y₁ f₁ V

local instance integralSource : Algebra S A := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X₂ U
local instance integralTarget : Algebra S D := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X₁ V
local instance residueSource : Algebra k C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k Y₂ (f₂ ⁻¹ᵁ U)
local instance residueTarget : Algebra k E := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k Y₁ (f₁ ⁻¹ᵁ V)

include sq hu in
omit [Fintype k] [CharP k p] [Smooth X₁.hom] [Smooth X₂.hom] in
theorem residue_refinement : f₁ ⁻¹ᵁ V ≤ v.left ⁻¹ᵁ (f₂ ⁻¹ᵁ U) :=
  AlgebraicGeometry.Crystalline.Cohomology.OpenSectionGeometricPullback.SectionGeometricSquare.preimage_le u.left v.left f₁ f₂ sq U V hu

def integralMap : A →ₐ[S] D := AlgebraicGeometry.Crystalline.Cohomology.OpenSectionGeometricPullback.DeRhamPullback.sectionPullbackLE u U V hu

def specialMap : C →ₐ[k] E := AlgebraicGeometry.Crystalline.Cohomology.OpenSectionGeometricPullback.DeRhamPullback.sectionPullbackLE v (f₂ ⁻¹ᵁ U) (f₁ ⁻¹ᵁ V)
  (residue_refinement p k n u v f₁ f₂ sq U V hu)

omit [Fintype k] [CharP k p] [Smooth X₁.hom] [Smooth X₂.hom] in
theorem reduction_square (a : A) :
    Truncated.AffineModelFrame.reduction p k n X₁ Y₁ f₁ V (integralMap p k n u U V hu a) =
      specialMap p k n u v f₁ f₂ sq U V hu (Truncated.AffineModelFrame.reduction p k n X₂ Y₂ f₂ U a) := by
  have h := AlgebraicGeometry.Crystalline.Cohomology.OpenSectionGeometricPullback.SectionGeometricSquare.square u.left v.left f₁ f₂ sq U V (f₂ ⁻¹ᵁ U) (f₁ ⁻¹ᵁ V)
    hu (residue_refinement p k n u v f₁ f₂ sq U V hu) le_rfl le_rfl
  rw [← f₁.app_eq_appLE, ← f₂.app_eq_appLE] at h
  exact ConcreteCategory.congr_hom h a

def geometricMap : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of C) :=
  Spec.map (CommRingCat.ofHom (specialMap p k n u v f₁ f₂ sq U V hu).toRingHom)

include hp₁ hp₂ hU hV in
omit [Smooth X₁.hom] [Smooth X₂.hom] in
theorem chart_square : geometricMap p k n u v f₁ f₂ sq U V hu ≫
    Truncated.AffineModelFrame.chart p k n X₂ Y₂ f₂ hp₂ U hU =
      Truncated.AffineModelFrame.chart p k n X₁ Y₁ f₁ hp₁ V hV ≫ v.left :=
  IsAffineOpen.SpecMap_appLE_fromSpec v.left
    (Truncated.AffineModelFrame.residue_affine p k n X₂ Y₂ f₂ hp₂ U hU)
    (Truncated.AffineModelFrame.residue_affine p k n X₁ Y₁ f₁ hp₁ V hV)
    (residue_refinement p k n u v f₁ f₂ sq U V hu)

omit [Fintype k] [CharP k p] [Smooth X₁.hom] [Smooth X₂.hom] in
theorem geometric_over : geometricMap p k n u v f₁ f₂ sq U V hu ≫
    Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C) =
      Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k E) :=
  Truncated.SmoothFrameMorphism.base_square p k C E (specialMap p k n u v f₁ f₂ sq U V hu)

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData.Frames

/-! Refined morphisms of actual finite-level models induce original
bounded crystalline frame maps with exactly their section ring maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [Smooth X₁.hom] [Smooth X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)
  (U : X₂.left.Opens) (V : X₁.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
  (hu : V ≤ u.left ⁻¹ᵁ U)

local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.sourceRing p k n X₂ U
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.sourceRing p k n X₁ V
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.targetRing p k n X₂ Y₂ f₂ U
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.targetRing p k n X₁ Y₁ f₁ V

local instance integralSource : Algebra S A := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X₂ U
local instance integralTarget : Algebra S D := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X₁ V
local instance residueSource : Algebra k C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k Y₂ (f₂ ⁻¹ᵁ U)
local instance residueTarget : Algebra k E := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k Y₁ (f₁ ⁻¹ᵁ V)

local notation "ψ" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData.geometricMap p k n u v f₁ f₂ sq U V hu
local notation "hψ" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData.geometric_over p k n u v f₁ f₂ sq U V hu
local notation "j₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.chart p k n X₁ Y₁ f₁ hp₁ V hV
local notation "j₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.chart p k n X₂ Y₂ f₂ hp₂ U hU

omit [Fintype k] [CharP k p] in
theorem ambient_over : v.left ≫ Witt.Crystalline.wittStructureMap p k Y₂ =
    Witt.Crystalline.wittStructureMap p k Y₁ := by
  rw [Witt.Crystalline.wittStructureMap, ← Category.assoc, v.w]
  rfl

def localMap :
    (BoundedOpen.Equivalence.postcompose ψ hψ n).obj
      (Truncated.AffineModelFrame.localFrame p k n X₁ Y₁ f₁ hp₁ V hV) ⟶
    Truncated.AffineModelFrame.localFrame p k n X₂ Y₂ f₂ hp₂ U hU := by
  let := Truncated.AffineModelFrame.source_smooth p k n X₂ U hU
  let := Truncated.AffineModelFrame.source_smooth p k n X₁ V hV
  exact Truncated.SmoothFrameMorphism.boundedMorphism p k n A D (integralMap p k n u U V hu) C E
    (Truncated.AffineModelFrame.reduction p k n X₂ Y₂ f₂ U)
    (Truncated.AffineModelFrame.reduction_surjective p k n X₂ Y₂ f₂ hp₂ U hU)
    (Truncated.AffineModelFrame.reduction_kernel p k n X₂ Y₂ f₂ hp₂ U hU)
    (Truncated.AffineModelFrame.reduction_base p k n X₂ Y₂ f₂ hp₂ U hU)
    (Truncated.AffineModelFrame.reduction p k n X₁ Y₁ f₁ V)
    (Truncated.AffineModelFrame.reduction_surjective p k n X₁ Y₁ f₁ hp₁ V hV)
    (Truncated.AffineModelFrame.reduction_kernel p k n X₁ Y₁ f₁ hp₁ V hV)
    (Truncated.AffineModelFrame.reduction_base p k n X₁ Y₁ f₁ hp₁ V hV)
    (specialMap p k n u v f₁ f₂ sq U V hu) (reduction_square p k n u v f₁ f₂ sq U V hu)

def map :
    (BoundedOpen.Equivalence.postcompose v.left (ambient_over p k v) n).obj
      (Truncated.AffineModelFrame.frame p k n X₁ Y₁ f₁ hp₁ V hV) ⟶
    Truncated.AffineModelFrame.frame p k n X₂ Y₂ f₂ hp₂ U hU :=
  ObjectProperty.homMk {
    ringMap := (localMap p k n u v f₁ f₂ hp₁ hp₂ sq U V hU hV hu).hom.ringMap
    overBase := (localMap p k n u v f₁ f₂ hp₁ hp₂ sq U V hU hV hu).hom.overBase
    overX := by
      let α := (localMap p k n u v f₁ f₂ hp₁ hp₂ sq U V hU hV hu).hom
      let c₁ := (Truncated.AffineModelFrame.localFrame p k n X₁ Y₁ f₁ hp₁ V hV).obj.mapToX
      change BigCrystallineSite.Object.closed.map α ≫
        ((Truncated.AffineModelFrame.localFrame p k n X₂ Y₂ f₂ hp₂ U hU).obj.mapToX ≫ j₂) =
          (c₁ ≫ j₁) ≫ v.left
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun m => m ≫ j₂) α.overX).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun m => c₁ ≫ m)
              (chart_square p k n u v f₁ f₂ hp₁ hp₂ sq U V hU hV hu)).trans
                (Category.assoc _ _ _).symm))) }

theorem map_ringMap : (Frames.map p k n u v f₁ f₂ hp₁ hp₂ sq U V hU hV hu).hom.ringMap =
    (localMap p k n u v f₁ f₂ hp₁ hp₂ sq U V hU hV hu).hom.ringMap := rfl

theorem map_apply (a : A) : (Frames.map p k n u v f₁ f₂ hp₁ hp₂ sq U V hU hV hu).hom.ringMap a =
    integralMap p k n u U V hu a := rfl

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData.Frames

end

end OAI
