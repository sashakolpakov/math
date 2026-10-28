import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.CoefficientTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralGlobalOne

/-! # Coefficient Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.CoefficientTotal.IntrinsicIntegralCoefficientTotal

noncomputable section

/-! The finite-level native comparison starts from coefficient transport
of the actual small integral Witt de Rham quotient Cech total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "coverOpens" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "coverNerve" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve coverOpens

def total : CochainComplex (ModuleCat.{0} W) ℕ :=
  CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total coverNerve (IntrinsicPadic.ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.source p X n)

def coefficientIso := CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso (IntrinsicPadic.IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.coefficients p)
  coverNerve (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices coverOpens)
    (IntrinsicPadic.ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.source p X n)

variable (J : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

def homologyIso :=
  (HomologicalComplex.homologyFunctor _ _ 1).mapIso (coefficientIso p X n) ≪≫
    IntrinsicPadic.IntegralGlobalOne.IntrinsicPadicIntegralGlobalHOne.homologyIso p X Y f hp n J

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.CoefficientTotal.IntrinsicIntegralCoefficientTotal
