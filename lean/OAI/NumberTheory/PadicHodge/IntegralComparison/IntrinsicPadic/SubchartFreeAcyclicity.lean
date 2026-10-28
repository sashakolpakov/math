import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.EtaleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFreeAcyclicity
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFrameDeRhamIso

/-! # Subchart Free Acyclicity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SubchartFreeAcyclicity.Intrinsic

noncomputable section

/-! The original p-adic subchart resolution terms are acyclic for
sections at every genuine bounded crystalline object. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ) (I : X.left.affineOpens) (i : GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X)
  (hi : I.val ≤ GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X i)

local notation "W" => WittVector p (ZMod p)
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X I.val
local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f I.val
local notation "σ" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.coordinateIndex ℤ_[p] X i
local instance padicAlgebra : Algebra ℤ_[p] A := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X I.val
local instance wittAlgebra : Algebra W A := GeometricComparison.WittAlgebra.PadicWittAlgebra.algebra p A
local instance specialAlgebra : Algebra (ZMod p) C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (ZMod p) Y (f ⁻¹ᵁ I.val)
local instance flat : Module.Flat W A := GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.source_flat p X I.val I.property
local notation "wI" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme (ZMod p) C)
local instance separated : IsSeparated wI := BoundedSmooth.WittFrameProduct.structureMap_separated p (ZMod p) C
local notation "FI" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.frame p X Y f hp I.val I.property n

variable (V : BoundedCrystalline.Site.Objects (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (Witt.Crystalline.wittStructureMap p (ZMod p)
    (Crystalline.Presentation.affineScheme (ZMod p)
      (GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f I.val))) n)

include hi in
theorem acyclic (a q : ℕ) : Subsingleton (Abelian.Ext.{2}
    (Bounded.FreeYonedaAcyclicity.source p (ZMod p) wI n V)
    ((Bounded.RelativeSheafComplex.complex wI n FI).X a) (q + 1)) := by
  let : Algebra (MvPolynomial σ W) A := GeometricComparison.IntrinsicPadic.EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.polynomialAlgebra p X I i hi
  let : IsScalarTower W (MvPolynomial σ W) A := GeometricComparison.IntrinsicPadic.EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.tower p X I i hi
  let : Algebra.Etale (MvPolynomial σ W) A := GeometricComparison.IntrinsicPadic.EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.etale p X I i hi
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  exact BoundedSmooth.WittFreeAcyclicity.positive_cohomology_zero p (ZMod p) A C σ
    (GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.reduction p X Y f I.val)
    (GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.reduction_surjective p X Y f hp I.val I.property)
    (GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.reduction_kernel p X Y f hp I.val I.property)
    (GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.reduction_base p X Y f hp I.val) n V a q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SubchartFreeAcyclicity.Intrinsic
