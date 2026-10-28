import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallCoefficientLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallQuotient
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.Coefficient
import OAI.NumberTheory.PadicHodge.GeometricComparison.NaturalTotalChain

/-! # Padic Small Coefficient Hodge -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicSmallCoefficientHodge.IntrinsicPadicSmallCoefficientHodge

noncomputable section

/-! The original small-to-large native coefficient comparison
preserves the form-degree Hodge image on Cech total H-one. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

private theorem totalIso_trans {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasCoproducts.{0} C] [HasCoproducts.{0} D]
    (F : C ⥤ D) [F.Additive] {K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)}
    {L M : HomologicalComplex₂ D (.up ℕ) (.up ℕ)}
    (e : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K ≅ L) (d : L ≅ M) :
    NaturalTotalCoefficient.NaturalTotalCoefficientHodge.totalIso F e ≪≫ HomologicalComplex₂.total.mapIso d (.up ℕ) =
      NaturalTotalCoefficient.NaturalTotalCoefficientHodge.totalIso F (e ≪≫ d) := by
  apply Iso.ext
  let T := HomologicalComplex₂.totalFunctor D (.up ℕ) (.up ℕ) (.up ℕ)
  exact (Category.assoc _ _ _).trans
    (congrArg (fun q => (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F K).inv ≫ q)
      (T.map_comp e.hom d.hom).symm)

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "hE" => OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.diagram p X n
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.source p X n
local notation "F" => ModuleCat.restrictScalars (RingEquiv.toRingHom (WittVector.equiv p))
local notation "G" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.coefficients p
local notation "FG" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p
local notation "B" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallQuotient.IntrinsicPadicSmallQuotientHodge.bicomplex p X n

def wittBicomplex : HomologicalComplex₂ (ModuleCat.{0} (WittVector p (ZMod p))) (.up ℕ) (.up ℕ) :=
  CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) Q)

def largeBicomplex : HomologicalComplex₂ (ModuleCat.{2} R) (.up ℕ) (.up ℕ) :=
  CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X n))

def wittBicomplexIso : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F B ≅ wittBicomplex p X n :=
  CechAssembly.Coefficient.CechAssemblyCoefficientHodge.bicomplexIso F E hE P ≪≫
    (CechAssembly.Iso.CechAssemblyIso.bicomplexIso E (Coefficient.IntrinsicPadicSmallQuotientTotal.wittIso p X n)).symm

def largeBicomplexIso : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G (wittBicomplex p X n) ≅ largeBicomplex p X n :=
  CechAssembly.Coefficient.CechAssemblyCoefficientHodge.bicomplexIso G E hE Q

def bicomplexIso : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex FG B ≅ largeBicomplex p X n :=
  NaturalTotalChain.NaturalTotalCoefficientComposition.bicomplexIso F G (wittBicomplexIso p X n) (largeBicomplexIso p X n)

theorem wittTotalIso_eq : (Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X n).symm =
    NaturalTotalCoefficient.NaturalTotalCoefficientHodge.totalIso F (wittBicomplexIso p X n) := by
  change CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso F E hE P ≪≫
    (CechAssembly.Iso.CechAssemblyIso.totalIso E (Coefficient.IntrinsicPadicSmallQuotientTotal.wittIso p X n)).symm = _
  rw [CechAssembly.Coefficient.CechAssemblyCoefficientHodge.iso_eq]
  exact totalIso_trans F (CechAssembly.Coefficient.CechAssemblyCoefficientHodge.bicomplexIso F E hE P)
    (CechAssembly.Iso.CechAssemblyIso.bicomplexIso E (Coefficient.IntrinsicPadicSmallQuotientTotal.wittIso p X n)).symm

theorem iso_eq : SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.iso p X n =
    NaturalTotalCoefficient.NaturalTotalCoefficientHodge.totalIso FG (bicomplexIso p X n) :=
  (congrArg (fun e => ((G).mapHomologicalComplex (.up ℕ)).mapIso e ≪≫
    IntrinsicIntegral.CoefficientTotal.IntrinsicIntegralCoefficientTotal.coefficientIso p X n) (wittTotalIso_eq p X n)).trans
      ((congrArg (fun e => ((G).mapHomologicalComplex (.up ℕ)).mapIso
        (NaturalTotalCoefficient.NaturalTotalCoefficientHodge.totalIso F (wittBicomplexIso p X n)) ≪≫ e)
        (CechAssembly.Coefficient.CechAssemblyCoefficientHodge.iso_eq G E hE Q)).trans
          (NaturalTotalChain.NaturalTotalCoefficientComposition.totalIso F G (wittBicomplexIso p X n) (largeBicomplexIso p X n)))

theorem homologyIso_eq : SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.homologyIso p X n =
    NaturalTotalCoefficient.NaturalTotalCoefficientHodge.homologyIso FG (bicomplexIso p X n) 1 :=
  congrArg (fun e => ExactHomology.ExactHomologyComparison.iso FG (.up ℕ)
    (Coefficient.IntrinsicPadicSmallQuotientTotal.total p X n) (SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.target p X n) e 1)
      (iso_eq p X n)

def truncatedHomologyIso (r : ℤ) :
    (FG).obj ((HomologicalComplex₂.total (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal B r) (.up ℕ)).homology 1) ≅
    (HomologicalComplex₂.total (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (largeBicomplex p X n) r) (.up ℕ)).homology 1 :=
  NaturalTotalCoefficient.NaturalTotalCoefficientHodge.homologyIso FG
    (NaturalTotalCoefficient.NaturalTotalCoefficientHodge.truncatedIso FG (bicomplexIso p X n) r) 1

theorem homology_inclusion (r : ℤ) :
    (FG).map (HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion B r) (.up ℕ)) 1) ≫
        (SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.homologyIso p X n).hom =
    (truncatedHomologyIso p X n r).hom ≫ HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (largeBicomplex p X n) r) (.up ℕ)) 1 := by
  rw [homologyIso_eq]
  exact NaturalTotalCoefficient.NaturalTotalCoefficientHodge.homology_inclusion FG (bicomplexIso p X n) 1 r

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicSmallCoefficientHodge.IntrinsicPadicSmallCoefficientHodge
