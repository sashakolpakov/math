import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusPrincipalZero
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineRestrictionPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCoordinates

/-! # Frobenius Reduction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusReduction.IntrinsicPadicFrobeniusHodgeReduction

noncomputable section

/-! The actual native first Hodge step reduces to classes killed by
original level-zero crystalline Frobenius under the constructed finite comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsProper Y.hom] [Smooth Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))
  (hprojective : IntegralComparison.Projectivity.Construction.ProjectiveOver (ZMod p) Y.hom)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X U
local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p
local notation "D" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicCoefficientDescent.restrict p

local notation "B" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex ℤ_[p] X U
local notation "g" => OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod p) Y

omit [Smooth Y.hom] in
theorem zero (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1)
    (hx : x ∈ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℤ_[p] X 1 1) :
    CrystallineRestrictionPullback.IntrinsicPadicCrystallineRestrictionPullback.pullback p Y g 0
      (CrystallineRestrictionExt.IntrinsicPadicIntegralCrystallineReduction.finiteEquiv p X Y f hp I 0
        (IntegralReductionCoordinates.IntrinsicPadicIntegralReductionCoordinates.reduction p X 1 x)) = 0 := by
  obtain ⟨a, ha⟩ := IntegralCoordinates.IntrinsicPadicIntegralHodgeCoordinates.exists_representative p X 1 x hx
  let i := HomologicalComplex.homologyMap
    (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion B 1) (.up ℕ)) 1
  let r := ModuleCat.ofHom (CochainQuotientCohomology.PrincipalCochainQuotient.reduction ℤ_[p] K (p : ℤ_[p]) 1 1)
  let e := PrincipalGlobalLevel.IntrinsicPadicPrincipalGlobalLevel.iso p X Y f hp I 0
  have h := congrArg (D).map (FrobeniusPrincipalZero.IntrinsicPadicFrobeniusPrincipalHodgeZero.homology p X Y f hp I)
  simp only [Functor.map_comp] at h
  have hz := ConcreteCategory.congr_hom h
    (Coefficient.IntrinsicPadicCoefficientDescent.equiv p ((HomologicalComplex₂.total
      (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal B 1) (.up ℕ)).homology 1) a)
  have he : CrystallineRestrictionExt.IntrinsicPadicIntegralCrystallineReduction.finiteEquiv p X Y f hp I 0
      (IntegralReductionCoordinates.IntrinsicPadicIntegralReductionCoordinates.reduction p X 1 x) =
      (D).map e.hom ((D).map ((F).map r) ((D).map ((F).map i)
        (Coefficient.IntrinsicPadicCoefficientDescent.equiv p ((HomologicalComplex₂.total
          (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal B 1) (.up ℕ)).homology 1) a))) := by
    change (D).map e.hom (Coefficient.IntrinsicPadicCoefficientDescent.equiv p
      ((PrincipalCochainExact.PrincipalCochainQuotient.quotient ℤ_[p] K (p : ℤ_[p]) 1).homology 1)
        (r (IntegralCechCoordinates.IntrinsicPadicIntegralCechCoordinates.equiv p X x))) = _
    rw [← ha]
    exact congrArg ((D).map e.hom)
      ((Coefficient.IntrinsicPadicCoefficientDescent.natural p r (i a)).trans
        (congrArg ((D).map ((F).map r)) (Coefficient.IntrinsicPadicCoefficientDescent.natural p i a)))
  exact (congrArg (CrystallineRestrictionPullback.IntrinsicPadicCrystallineRestrictionPullback.pullback p Y g 0) he).trans hz

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusReduction.IntrinsicPadicFrobeniusHodgeReduction
