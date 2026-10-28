import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.EtaleCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.WittCoefficientReductionIso

/-! # Reduced De Rham Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamIso.IntrinsicPadicReducedDeRhamIso

noncomputable section

/-! The canonical reduction into the native PD-frame diagram is an
isomorphism on every affine subchart of the integral etale coordinate cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ) (I : X.left.affineOpens) (i : Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X)
  (hi : I.val ≤ Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X i)

local notation "W" => WittVector p (ZMod p)
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X I.val
local notation "σ" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.coordinateIndex ℤ_[p] X i
local instance padicAlgebra : Algebra ℤ_[p] A := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X I.val
local instance wittAlgebra : Algebra W A := WittAlgebra.PadicWittAlgebra.algebra p A

include hi in
theorem ordinary_component_isIso : IsIso
    ((ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.ordinaryTransformation p X Y f hp n).app (Opposite.op I)) := by
  let : Algebra (MvPolynomial σ W) A := EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.polynomialAlgebra p X I i hi
  let : IsScalarTower W (MvPolynomial σ W) A := EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.tower p X I i hi
  let : Algebra.Etale (MvPolynomial σ W) A := EtaleCoordinates.IntrinsicPadicEtaleSubchartCoordinates.etale p X I i hi
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  exact GeometricComparison.Smooth.WittCoefficientReductionIso.SmoothWittCoefficientReductionIso.isIso p (ZMod p) A σ n
    (QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.annihilation p X Y f hp n (Opposite.op I))

include hi in
theorem pd_component_isIso : IsIso
    ((ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.pdTransformation p X Y f hp n).app (Opposite.op I)) := by
  let := ordinary_component_isIso p X Y f hp n I i hi
  change IsIso (((ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.ordinaryTransformation p X Y f hp n).app (Opposite.op I)) ≫
    (PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.iso p X Y f hp n).inv.app (Opposite.op I))
  infer_instance

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamIso.IntrinsicPadicReducedDeRhamIso
