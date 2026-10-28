import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineReductionRing
import OAI.NumberTheory.PadicHodge.GeometricComparison.WittAlgebra
import OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.IntegralFirstThreeSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame

/-! # Affine Frame -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame

noncomputable section

/-! Actual affine sections of the integral model and its special fiber define
the original finite Witt crystalline frames. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
local instance residueAlgebra : Algebra ℤ_[p] (ZMod p) := PadicInt.toZMod.toAlgebra

variable (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (U : X.left.Opens) (hU : IsAffineOpen U)

abbrev sourceRing : Type := Γ(X.left, U)
abbrev targetRing : Type := Γ(Y.left, f ⁻¹ᵁ U)

local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U
local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f U
local notation "W" => WittVector p (ZMod p)

local instance padicAlgebra : Algebra ℤ_[p] A := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X U
local instance specialAlgebra : Algebra (ZMod p) C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (ZMod p) Y (f ⁻¹ᵁ U)
local instance wittAlgebra : Algebra W A := WittAlgebra.PadicWittAlgebra.algebra p A

include hU in
theorem source_smooth : Algebra.Smooth W A := by
  let : Algebra.Smooth ℤ_[p] A := GeometricComparison.Smooth.IntegralFirstThreeSections.SmoothIntegralFirstThreeSections.algebra_smooth ℤ_[p] X U hU
  exact WittAlgebra.PadicWittAlgebra.smooth p A

include hU in
theorem source_flat : Module.Flat W A := by
  let : Algebra.Smooth W A := source_smooth p X U hU
  infer_instance

def reduction : A →+* C := (f.app U).hom

include hp hU in
omit [Smooth X.hom] in
theorem reduction_surjective : Function.Surjective (reduction p X Y f U) :=
  Intrinsic.AffineReductionRing.IntrinsicAffineReductionRing.surjective ℤ_[p] (ZMod p) X Y f hp U hU
    (ZMod.ringHom_surjective PadicInt.toZMod)

include hp hU in
omit [Smooth X.hom] in
theorem reduction_kernel : RingHom.ker (reduction p X Y f U) = Ideal.span {(p : A)} := by
  have h := Intrinsic.AffineReductionRing.IntrinsicAffineReductionRing.kernel_principal ℤ_[p] (ZMod p) X Y f hp U hU
    (ZMod.ringHom_surjective PadicInt.toZMod) (p : ℤ_[p])
    (PadicInt.ker_toZMod.trans PadicInt.maximalIdeal_eq_span_p)
  simpa only [reduction, sourceRing, map_natCast] using h

include hp in
omit [Smooth X.hom] in
theorem reduction_base (w : W) :
    reduction p X Y f U (algebraMap W A w) = algebraMap (ZMod p) C (WittVector.constantCoeff w) :=
  WittAlgebra.PadicWittAlgebra.reduction_base p A C (reduction p X Y f U)
    (Intrinsic.AffineReductionRing.IntrinsicAffineReductionRing.base ℤ_[p] (ZMod p) X Y f hp U) w

def frame (n : ℕ) := by
  letI : Module.Flat W A := source_flat p X U hU
  exact IntegralComparison.SmoothWitt.WittFrame.boundedFrame p (ZMod p) A C
    (reduction p X Y f U) (reduction_surjective p X Y f hp U hU)
    (reduction_kernel p X Y f hp U hU) (reduction_base p X Y f hp U) n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame
