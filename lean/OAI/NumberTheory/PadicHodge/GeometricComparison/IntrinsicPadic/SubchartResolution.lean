import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.EtaleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittAcyclicTerms
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFrameDeRhamIso

/-! # Subchart Resolution -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SubchartResolution.IntrinsicPadicSubchartResolution

noncomputable section

/-! The original native frame of each affine subchart is an acyclic
resolution whose actual section map is invertible. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ) (I : X.left.affineOpens) (i : Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X)
  (hi : I.val ≤ Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X i)

local notation "W" => WittVector p (ZMod p)
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X I.val
local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f I.val
local notation "σ" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.coordinateIndex ℤ_[p] X i
local instance padicAlgebra : Algebra ℤ_[p] A := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X I.val
local instance wittAlgebra : Algebra W A := WittAlgebra.PadicWittAlgebra.algebra p A
local instance specialAlgebra : Algebra (ZMod p) C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (ZMod p) Y (f ⁻¹ᵁ I.val)
local instance flat : Module.Flat W A := AffineFrame.IntrinsicPadicAffineFrame.source_flat p X I.val I.property
local notation "wI" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme (ZMod p) C)
local instance separated : IsSeparated wI := IntegralComparison.BoundedSmooth.WittFrameProduct.structureMap_separated p (ZMod p) C
local notation "FI" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.frame p X Y f hp I.val I.property n

include hi in
theorem augmentation_quasiIso : QuasiIso (IntegralComparison.Bounded.RelativeSheafComplex.augmentation wI n FI) := by
  let : Algebra (MvPolynomial σ W) A := EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.polynomialAlgebra p X I i hi
  let : IsScalarTower W (MvPolynomial σ W) A := EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.tower p X I i hi
  let : Algebra.Etale (MvPolynomial σ W) A := EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.etale p X I i hi
  exact IntegralComparison.BoundedSmooth.WittResolution.augmentation_quasiIso p (ZMod p) A C σ
    (AffineFrame.IntrinsicPadicAffineFrame.reduction p X Y f I.val)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_surjective p X Y f hp I.val I.property)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_kernel p X Y f hp I.val I.property)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_base p X Y f hp I.val) n

include hi in
theorem acyclic (a q : ℕ) : Subsingleton (Abelian.Ext.{2}
    (IntegralComparison.BoundedCrystalline.CrystallineCohomology.constantUnit wI n)
    ((IntegralComparison.Bounded.RelativeSheafComplex.complex wI n FI).X a) (q + 1)) := by
  let : Algebra (MvPolynomial σ W) A := EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.polynomialAlgebra p X I i hi
  let : IsScalarTower W (MvPolynomial σ W) A := EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.tower p X I i hi
  let : Algebra.Etale (MvPolynomial σ W) A := EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.etale p X I i hi
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  exact IntegralComparison.BoundedSmooth.WittAcyclicTerms.positive_cohomology_zero p (ZMod p) A C σ
    (AffineFrame.IntrinsicPadicAffineFrame.reduction p X Y f I.val)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_surjective p X Y f hp I.val I.property)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_kernel p X Y f hp I.val I.property)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_base p X Y f hp I.val) n a q

include hi in
theorem sectionsMap_isIso : IsIso (IntegralComparison.BoundedFrame.DeRhamSections.sectionsMap wI n FI) := by
  let : Algebra (MvPolynomial σ W) A := EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.polynomialAlgebra p X I i hi
  let : IsScalarTower W (MvPolynomial σ W) A := EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.tower p X I i hi
  let : Algebra.Etale (MvPolynomial σ W) A := EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.etale p X I i hi
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  exact IntegralComparison.BoundedSmooth.WittFrameDeRhamIso.sectionsMap_isIso p (ZMod p) A C σ
    (AffineFrame.IntrinsicPadicAffineFrame.reduction p X Y f I.val)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_surjective p X Y f hp I.val I.property)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_kernel p X Y f hp I.val I.property)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_base p X Y f hp I.val) n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SubchartResolution.IntrinsicPadicSubchartResolution
