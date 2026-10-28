import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData
import OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.WittFrameMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.Postcomposition

/-! # Frame Map -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameMap.IntrinsicPadicFrameGeometricMap

/-! Arbitrary compatible geometric maps of the actual integral models
induce the original bounded crystalline frame map with its quotient-ring formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))} [Smooth X₁.hom] [Smooth X₂.hom]
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

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData

local notation "g" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData.geometricMap p u v f₁ f₂ hsquare U V hu
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData.geometric_over_witt p u v f₁ f₂ hp₁ hp₂ hsquare U V hU hV hu

def localMap (n : ℕ) :
    (IntegralComparison.BoundedOpen.Equivalence.postcompose g hg n).obj (AffineFrame.IntrinsicPadicAffineFrame.frame p X₁ Y₁ f₁ hp₁ V hV n) ⟶
      AffineFrame.IntrinsicPadicAffineFrame.frame p X₂ Y₂ f₂ hp₂ U hU n := by
  let : Module.Flat W A := AffineFrame.IntrinsicPadicAffineFrame.source_flat p X₂ U hU
  let : Module.Flat W B := AffineFrame.IntrinsicPadicAffineFrame.source_flat p X₁ V hV
  exact GeometricComparison.Smooth.WittFrameMap.SmoothWittFrameGeometricMap.boundedMorphism p (ZMod p) A B C D
    (AffineFrame.IntrinsicPadicAffineFrame.reduction p X₂ Y₂ f₂ U)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_surjective p X₂ Y₂ f₂ hp₂ U hU)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_kernel p X₂ Y₂ f₂ hp₂ U hU)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_base p X₂ Y₂ f₂ hp₂ U)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction p X₁ Y₁ f₁ V)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_surjective p X₁ Y₁ f₁ hp₁ V hV)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_kernel p X₁ Y₁ f₁ hp₁ V hV)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_base p X₁ Y₁ f₁ hp₁ V)
    (FrameData.IntrinsicPadicFrameGeometricData.integralMap p u U V hu) (FrameData.IntrinsicPadicFrameGeometricData.specialMap p u v f₁ f₂ hsquare U V hu).toRingHom
    (FrameData.IntrinsicPadicFrameGeometricData.reduction_square p u v f₁ f₂ hsquare U V hu) g hg rfl n

def map (n : ℕ) :
    (IntegralComparison.BoundedOpen.Equivalence.postcompose v.left (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n).obj
      (ChartImage.IntrinsicPadicOpenFrame.frame p X₁ Y₁ f₁ hp₁ V hV n) ⟶
        ChartImage.IntrinsicPadicOpenFrame.frame p X₂ Y₂ f₂ hp₂ U hU n :=
  Crystalline.Postcomposition.CrystallineFrameGeometricPostcomposition.map g v.left
    (ChartImage.IntrinsicPadicOpenFrame.chart p X₁ Y₁ f₁ hp₁ V hV)
    (ChartImage.IntrinsicPadicOpenFrame.chart p X₂ Y₂ f₂ hp₂ U hU)
    hg (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v)
    (ChartImage.IntrinsicPadicOpenFrame.chart_over_witt p X₁ Y₁ f₁ hp₁ V hV)
    (ChartImage.IntrinsicPadicOpenFrame.chart_over_witt p X₂ Y₂ f₂ hp₂ U hU)
    (FrameData.IntrinsicPadicFrameGeometricData.chart_square p u v f₁ f₂ hp₁ hp₂ hsquare U V hU hV hu) n
    (localMap p u v f₁ f₂ hp₁ hp₂ hsquare U V hU hV hu n)

theorem map_ringMap (n : ℕ) :
    (IntrinsicPadicFrameGeometricMap.map p u v f₁ f₂ hp₁ hp₂ hsquare U V hU hV hu n).hom.ringMap =
      (localMap p u v f₁ f₂ hp₁ hp₂ hsquare U V hU hV hu n).hom.ringMap :=
  Crystalline.Postcomposition.CrystallineFrameGeometricPostcomposition.ringMap g v.left
    (ChartImage.IntrinsicPadicOpenFrame.chart p X₁ Y₁ f₁ hp₁ V hV)
    (ChartImage.IntrinsicPadicOpenFrame.chart p X₂ Y₂ f₂ hp₂ U hU)
    hg (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v)
    (ChartImage.IntrinsicPadicOpenFrame.chart_over_witt p X₁ Y₁ f₁ hp₁ V hV)
    (ChartImage.IntrinsicPadicOpenFrame.chart_over_witt p X₂ Y₂ f₂ hp₂ U hU)
    (FrameData.IntrinsicPadicFrameGeometricData.chart_square p u v f₁ f₂ hp₁ hp₂ hsquare U V hU hV hu) n
    (localMap p u v f₁ f₂ hp₁ hp₂ hsquare U V hU hV hu n)

theorem map_mk (n : ℕ) (a : A) :
    (IntrinsicPadicFrameGeometricMap.map p u v f₁ f₂ hp₁ hp₂ hsquare U V hU hV hu n).hom.ringMap
      (Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ (n + 1)) a) =
        Ideal.Quotient.mk ((Ideal.span {(p : B)}) ^ (n + 1)) (FrameData.IntrinsicPadicFrameGeometricData.integralMap p u U V hu a) := by
  rw [map_ringMap]
  rfl

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameMap.IntrinsicPadicFrameGeometricMap

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameMap.IntrinsicPadicFrameGeometricRingCoordinates

/-! Global and local geometric native frame maps have the same
unapplied ring homomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))} [Smooth X₁.hom] [Smooth X₂.hom]
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

theorem ringHom (n : ℕ) :
    (IntrinsicPadicFrameGeometricMap.map p u v f₁ f₂ hp₁ hp₂ hsquare U V hU hV hu n).hom.ringMap.toRingHom =
      (IntrinsicPadicFrameGeometricMap.localMap p u v f₁ f₂ hp₁ hp₂ hsquare U V hU hV hu n).hom.ringMap.toRingHom :=
  congrArg DividedPowers.DPMorphism.toRingHom
    (IntrinsicPadicFrameGeometricMap.map_ringMap p u v f₁ f₂ hp₁ hp₂ hsquare U V hU hV hu n)

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameMap.IntrinsicPadicFrameGeometricRingCoordinates

end

end OAI
