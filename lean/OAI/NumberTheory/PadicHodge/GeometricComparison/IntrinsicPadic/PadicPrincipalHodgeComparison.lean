import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicSmallCoefficientHodge
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalCoefficientLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalTruncation

/-! # Padic Principal Hodge Comparison -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicPrincipalHodgeComparison.IntrinsicPadicPrincipalHodgeComparison

noncomputable section

/-! Original integral principal reduction followed by the actual native
source comparison factors through the original reduced source Hodge inclusion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X)
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "B" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex ℤ_[p] X U
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (ComplexShape.up ℕ) (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X n)
local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p

def map (r : ℤ) : (F).obj ((HomologicalComplex₂.total (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal B r) (.up ℕ)).homology 1) ⟶
    (((Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} R E).obj (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r)).total (.up ℕ)).homology 1 :=
  (F).map (SmallQuotient.IntrinsicPadicSmallQuotientHodge.truncatedMap p X n r) ≫
    (PadicSmallCoefficientHodge.IntrinsicPadicSmallCoefficientHodge.truncatedHomologyIso p X n r).hom ≫
      HomologicalComplex.homologyMap (Cech.TotalTruncation.CechTotalHodgeTruncation.totalIso.{1, 2} R E K r).inv 1

theorem inclusion (r : ℤ) :
    (F).map (HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion B r) (.up ℕ)) 1) ≫
    (F).map (ModuleCat.ofHom (CochainQuotientCohomology.PrincipalCochainQuotient.reduction ℤ_[p]
      (IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X U) (p : ℤ_[p]) (n + 1) 1)) ≫
      (PrincipalCoefficientLevel.IntrinsicPadicPrincipalCoefficientLevel.iso p X n).hom =
    IntrinsicPadicPrincipalHodgeComparison.map p X n r ≫ HomologicalComplex.homologyMap
      (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R E (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r)) 1 := by
  let i := (F).map (HomologicalComplex.homologyMap
    (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion B r) (.up ℕ)) 1)
  let a := (F).map (ModuleCat.ofHom (CochainQuotientCohomology.PrincipalCochainQuotient.reduction ℤ_[p]
    (IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X U) (p : ℤ_[p]) (n + 1) 1))
  let b := (F).map (FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X n).inv
  let c := (SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.homologyIso p X n).hom
  let d := (F).map (SmallQuotient.IntrinsicPadicSmallQuotientHodge.truncatedMap p X n r)
  let j := (F).map (HomologicalComplex.homologyMap
    (HomologicalComplex₂.total.map
      (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (SmallQuotient.IntrinsicPadicSmallQuotientHodge.bicomplex p X n) r) (.up ℕ)) 1)
  let e := (PadicSmallCoefficientHodge.IntrinsicPadicSmallCoefficientHodge.truncatedHomologyIso p X n r).hom
  let k := HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (PadicSmallCoefficientHodge.IntrinsicPadicSmallCoefficientHodge.largeBicomplex p X n) r) (.up ℕ)) 1
  have h₁ : i ≫ (a ≫ b) = d ≫ j := by
    have h := congrArg (F).map (SmallQuotient.IntrinsicPadicSmallQuotientHodge.inclusion p X n r)
    simp only [Functor.map_comp] at h
    exact h
  have h₂ : j ≫ c = e ≫ k := PadicSmallCoefficientHodge.IntrinsicPadicSmallCoefficientHodge.homology_inclusion p X n r
  have h := ExactHomology.ExactHomologyComparison.compose i (a ≫ b) c d j e k h₁ h₂
  have h₃ : k = HomologicalComplex.homologyMap (Cech.TotalTruncation.CechTotalHodgeTruncation.totalIso.{1, 2} R E K r).inv 1 ≫
      HomologicalComplex.homologyMap (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R E (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r)) 1 :=
    (congrArg (fun a => HomologicalComplex.homologyMap a 1)
      (Cech.TotalTruncation.CechTotalHodgeTruncation.inverse_inclusion.{1, 2} R E K r)).trans
        (HomologicalComplex.homologyMap_comp (Cech.TotalTruncation.CechTotalHodgeTruncation.totalIso.{1, 2} R E K r).inv
          (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R E (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r)) 1)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (ConcreteCategory.congr_hom h x).trans (ConcreteCategory.congr_hom h₃ ((d ≫ e) x))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicPrincipalHodgeComparison.IntrinsicPadicPrincipalHodgeComparison
