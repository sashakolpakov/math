import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.GeometricRestriction

/-! # Frame Data -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData

noncomputable section

/-! Compatible geometric maps of integral models and special fibers
give the actual section-ring maps on any compatible pair of affine opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂)
  (U : X₂.left.Opens) (V : X₁.left.Opens)
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hu : V ≤ u.left ⁻¹ᵁ U)

local notation "W" => WittVector p (ZMod p)
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X₂ U
local notation "B" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X₁ V
local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.targetRing p X₂ Y₂ f₂ U
local notation "D" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.targetRing p X₁ Y₁ f₁ V

local instance padicA : Algebra ℤ_[p] A := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X₂ U
local instance padicB : Algebra ℤ_[p] B := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X₁ V
local instance wittA : Algebra W A := WittAlgebra.PadicWittAlgebra.algebra p A
local instance wittB : Algebra W B := WittAlgebra.PadicWittAlgebra.algebra p B
local instance specialC : Algebra (ZMod p) C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (ZMod p) Y₂ (f₂ ⁻¹ᵁ U)
local instance specialD : Algebra (ZMod p) D := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (ZMod p) Y₁ (f₁ ⁻¹ᵁ V)

def integralMap : A →ₐ[W] B :=
  { (OpenSectionPullback.DeRham.sectionPullbackLE u U V hu).toRingHom with
    commutes' := fun w => (OpenSectionPullback.DeRham.sectionPullbackLE u U V hu).commutes ((WittVector.equiv p) w) }

def specialMap : C →ₐ[ZMod p] D :=
  OpenSectionPullback.DeRham.sectionPullbackLE v (f₂ ⁻¹ᵁ U) (f₁ ⁻¹ᵁ V)
    (Section.GeometricRestriction.SectionGeometricSquare.preimage_le u.left v.left f₁ f₂ hsquare U V hu)

theorem reduction_square (a : A) :
    AffineFrame.IntrinsicPadicAffineFrame.reduction p X₁ Y₁ f₁ V (integralMap p u U V hu a) =
      specialMap p u v f₁ f₂ hsquare U V hu (AffineFrame.IntrinsicPadicAffineFrame.reduction p X₂ Y₂ f₂ U a) := by
  change (f₁.app V) ((u.left.appLE U V hu) a) =
    (v.left.appLE (f₂ ⁻¹ᵁ U) (f₁ ⁻¹ᵁ V)
      (Section.GeometricRestriction.SectionGeometricSquare.preimage_le u.left v.left f₁ f₂ hsquare U V hu)) ((f₂.app U) a)
  have h := Section.GeometricRestriction.SectionGeometricSquare.square u.left v.left f₁ f₂ hsquare U V
    (f₂ ⁻¹ᵁ U) (f₁ ⁻¹ᵁ V) hu
    (Section.GeometricRestriction.SectionGeometricSquare.preimage_le u.left v.left f₁ f₂ hsquare U V hu) le_rfl le_rfl
  simpa only [Scheme.Hom.appLE_eq_app, CommRingCat.comp_apply] using ConcreteCategory.congr_hom h a

def geometricMap : (IntegralComparison.Crystalline.Presentation.affineScheme (ZMod p) D).left ⟶ (IntegralComparison.Crystalline.Presentation.affineScheme (ZMod p) C).left :=
  Spec.map (CommRingCat.ofHom (specialMap p u v f₁ f₂ hsquare U V hu).toRingHom)

include hp₁ hp₂ hU hV in
theorem chart_square : geometricMap p u v f₁ f₂ hsquare U V hu ≫
    ChartImage.IntrinsicPadicOpenFrame.chart p X₂ Y₂ f₂ hp₂ U hU =
      ChartImage.IntrinsicPadicOpenFrame.chart p X₁ Y₁ f₁ hp₁ V hV ≫ v.left :=
  IsAffineOpen.SpecMap_appLE_fromSpec v.left
    (ChartImage.IntrinsicPadicOpenFrame.special_affine p X₂ Y₂ f₂ hp₂ U hU)
    (ChartImage.IntrinsicPadicOpenFrame.special_affine p X₁ Y₁ f₁ hp₁ V hV)
    (Section.GeometricRestriction.SectionGeometricSquare.preimage_le u.left v.left f₁ f₂ hsquare U V hu)

theorem global_over_witt : v.left ≫ IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂ = IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁ := by
  simp only [IntegralComparison.Witt.Crystalline.wittStructureMap, ← Category.assoc, Over.w]

include hp₁ hp₂ hU hV in
theorem geometric_over_witt : geometricMap p u v f₁ f₂ hsquare U V hu ≫
    IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) (IntegralComparison.Crystalline.Presentation.affineScheme (ZMod p) C) =
      IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) (IntegralComparison.Crystalline.Presentation.affineScheme (ZMod p) D) := by
  rw [← ChartImage.IntrinsicPadicOpenFrame.chart_over_witt p X₂ Y₂ f₂ hp₂ U hU, ← Category.assoc,
    chart_square p u v f₁ f₂ hp₁ hp₂ hsquare U V hU hV hu, Category.assoc,
    global_over_witt p v, ChartImage.IntrinsicPadicOpenFrame.chart_over_witt]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData
