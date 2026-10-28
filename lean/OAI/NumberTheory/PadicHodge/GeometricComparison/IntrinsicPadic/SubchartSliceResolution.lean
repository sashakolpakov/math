import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.EtaleCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.WittGlobalSliceResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage

/-! # Subchart Slice Resolution -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SubchartSliceResolution.IntrinsicPadicSubchartSliceResolution

noncomputable section

/-! On every affine subchart of the actual integral coordinate cover, the original
native Witt frame augmentation resolves the structure presheaf on its slice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ) (I : X.left.affineOpens) (i : Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X)
  (hi : I.val ≤ Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X i)

local notation "W" => WittVector p (ZMod p)
local notation "U" => Subtype.val I
local notation "hU" => Subtype.property I
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U
local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f U
local notation "σ" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.coordinateIndex ℤ_[p] X i
local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp U hU n

local instance padicAlgebra : Algebra ℤ_[p] A := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X U
local instance wittAlgebra : Algebra W A := WittAlgebra.PadicWittAlgebra.algebra p A
local instance specialAlgebra : Algebra (ZMod p) C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (ZMod p) Y (f ⁻¹ᵁ U)
local instance separated : IsSeparated (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

local instance chartOpen : IsOpenImmersion (ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp U hU) :=
  ChartImage.IntrinsicPadicOpenFrame.chart_open p X Y f hp U hU

include hi in
theorem onSlice : QuasiIso
    (((PresheafRestriction.PresheafRestrictionQuasiIso.restriction (V := ModuleCat W)
      (Over.forget F)).mapHomologicalComplex (.up ℕ)).map
        (IntegralComparison.BoundedFrame.Diagram.augmentation F)) := by
  let : Module.Flat W A := AffineFrame.IntrinsicPadicAffineFrame.source_flat p X U hU
  let : Algebra (MvPolynomial σ W) A := EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.polynomialAlgebra p X I i hi
  let : IsScalarTower W (MvPolynomial σ W) A := EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.tower p X I i hi
  let : Algebra.Etale (MvPolynomial σ W) A := EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.etale p X I i hi
  exact GeometricComparison.Smooth.WittGlobalSliceResolution.SmoothWittGlobalSliceResolution.onSlice p (ZMod p) A C σ
    (AffineFrame.IntrinsicPadicAffineFrame.reduction p X Y f U)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_surjective p X Y f hp U hU)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_kernel p X Y f hp U hU)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_base p X Y f hp U) n
    (ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp U hU) (ChartImage.IntrinsicPadicOpenFrame.chart_over_witt p X Y f hp U hU)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SubchartSliceResolution.IntrinsicPadicSubchartSliceResolution
