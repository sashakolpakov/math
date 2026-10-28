import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.PDTruncationLevel

/-! # Frame Level Square -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelSquare.IntrinsicPadicFrameLevelRingNaturality

/-! Unapplied ring-homomorphism coordinates for native frame reduction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (U V : X.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ V)
  (n m : ℕ) (hnm : n ≤ m)

local notation "W" => WittVector p (ZMod p)
local notation "AU" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U
local notation "AV" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X V

local instance padicU : Algebra ℤ_[p] AU := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X U
local instance padicV : Algebra ℤ_[p] AV := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X V
local instance wittU : Algebra W AU := WittAlgebra.PadicWittAlgebra.algebra p AU
local instance wittV : Algebra W AV := WittAlgebra.PadicWittAlgebra.algebra p AV

theorem level_ringHom : (FrameLevelMap.IntrinsicPadicFrameLevelMap.map p X Y f hp U hU n m hnm).hom.ringMap.toRingHom =
    IntegralComparison.PD.TruncationTransition.map AU (Ideal.span {(p : AU)}) n m hnm := rfl

theorem local_natural :
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.localMap p X Y f hp U V hU hV hUV n).hom.ringMap.toRingHom.comp
      (IntegralComparison.PD.TruncationTransition.map AV (Ideal.span {(p : AV)}) n m hnm) =
    (IntegralComparison.PD.TruncationTransition.map AU (Ideal.span {(p : AU)}) n m hnm).comp
      (PadicFrameRestriction.IntrinsicPadicFrameRestriction.localMap p X Y f hp U V hU hV hUV m).hom.ringMap.toRingHom := by
  let := AffineFrame.IntrinsicPadicAffineFrame.source_flat p X U hU
  let := AffineFrame.IntrinsicPadicAffineFrame.source_flat p X V hV
  exact PDTruncationLevel.PDTruncationMap.level_naturality
    (GeometricComparison.Smooth.WittFrameMap.SmoothWittFrameGeometricMap.integralDPMap p (ZMod p) AV AU
      (FrameRestrictionData.IntrinsicPadicFrameRestrictionData.integralMap p X U V hUV)) n m hnm

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelSquare.IntrinsicPadicFrameLevelRingNaturality

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelSquare.IntrinsicPadicFrameLevelRawSquare

/-! The native global frame square follows from the actual local ring maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (U V : X.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ V)
  (n m : ℕ) (hnm : n ≤ m)

local notation "AU" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U
local notation "AV" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X V

theorem restriction_ringHom (q : ℕ) :
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV q).hom.ringMap.toRingHom =
      (PadicFrameRestriction.IntrinsicPadicFrameRestriction.localMap p X Y f hp U V hU hV hUV q).hom.ringMap.toRingHom :=
  congrArg DividedPowers.DPMorphism.toRingHom (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map_ringMap p X Y f hp U V hU hV hUV q)

theorem left_coordinates :
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV n).hom.ringMap.toRingHom.comp
      (FrameLevelMap.IntrinsicPadicFrameLevelMap.map p X Y f hp V hV n m hnm).hom.ringMap.toRingHom =
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.localMap p X Y f hp U V hU hV hUV n).hom.ringMap.toRingHom.comp
      (IntegralComparison.PD.TruncationTransition.map AV (Ideal.span {(p : AV)}) n m hnm) :=
  congrArg₂ (fun (a : AV ⧸ (Ideal.span {(p : AV)}) ^ (n + 1) →+* AU ⧸ (Ideal.span {(p : AU)}) ^ (n + 1))
    (b : AV ⧸ (Ideal.span {(p : AV)}) ^ (m + 1) →+* AV ⧸ (Ideal.span {(p : AV)}) ^ (n + 1)) => a.comp b)
    (restriction_ringHom p X Y f hp U V hU hV hUV n)
    (IntrinsicPadicFrameLevelRingNaturality.level_ringHom p X Y f hp V hV n m hnm)

theorem right_coordinates :
    (FrameLevelMap.IntrinsicPadicFrameLevelMap.map p X Y f hp U hU n m hnm).hom.ringMap.toRingHom.comp
      (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV m).hom.ringMap.toRingHom =
    (IntegralComparison.PD.TruncationTransition.map AU (Ideal.span {(p : AU)}) n m hnm).comp
      (PadicFrameRestriction.IntrinsicPadicFrameRestriction.localMap p X Y f hp U V hU hV hUV m).hom.ringMap.toRingHom :=
  congrArg₂ (fun (a : AU ⧸ (Ideal.span {(p : AU)}) ^ (m + 1) →+* AU ⧸ (Ideal.span {(p : AU)}) ^ (n + 1))
    (b : AV ⧸ (Ideal.span {(p : AV)}) ^ (m + 1) →+* AU ⧸ (Ideal.span {(p : AU)}) ^ (m + 1)) => a.comp b)
    (IntrinsicPadicFrameLevelRingNaturality.level_ringHom p X Y f hp U hU n m hnm)
    (restriction_ringHom p X Y f hp U V hU hV hUV m)

theorem ringHom :
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV n).hom.ringMap.toRingHom.comp
      (FrameLevelMap.IntrinsicPadicFrameLevelMap.map p X Y f hp V hV n m hnm).hom.ringMap.toRingHom =
    (FrameLevelMap.IntrinsicPadicFrameLevelMap.map p X Y f hp U hU n m hnm).hom.ringMap.toRingHom.comp
      (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV m).hom.ringMap.toRingHom :=
  (left_coordinates p X Y f hp U V hU hV hUV n m hnm).trans
    ((IntrinsicPadicFrameLevelRingNaturality.local_natural p X Y f hp U V hU hV hUV n m hnm).trans
      (right_coordinates p X Y f hp U V hU hV hUV n m hnm).symm)

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelSquare.IntrinsicPadicFrameLevelRawSquare

end

end OAI
