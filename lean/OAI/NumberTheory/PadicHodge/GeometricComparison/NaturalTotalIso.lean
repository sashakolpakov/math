import OAI.NumberTheory.PadicHodge.GeometricComparison.TruncatedFunctorIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor

/-! # Natural Total Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.NaturalTotalIso.NaturalTotalHodgeIso

noncomputable section

/-! An actual bicomplex isomorphism and its inverse preserve every
outer-degree Hodge inclusion on the nonnegative total cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable (R : Type u) [CommRing R]
  {K L : HomologicalComplex₂ (ModuleCat.{max u v} R) (.up ℕ) (.up ℕ)} (e : K ≅ L)

local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasColimitsOfSize.{max u v, u, 0, 0} R

def truncatedIso (r : ℤ) : AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r ≅ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r :=
  TruncatedFunctorIso.TruncatedPullback.iso (𝟭 (CochainComplex (ModuleCat.{max u v} R) ℕ)) e r

def homologyIso (n : ℕ) : (K.total (.up ℕ)).homology n ≅ (L.total (.up ℕ)).homology n :=
  HomologicalComplex.homologyMapIso (HomologicalComplex₂.total.mapIso e (.up ℕ)) n

theorem inclusion (n : ℕ) (r : ℤ) :
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) (.up ℕ)) n ≫
      (homologyIso R e n).hom =
    (homologyIso R (truncatedIso R e r) n).hom ≫
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r) (.up ℕ)) n := by
  let T := HomologicalComplex₂.totalFunctor (ModuleCat.{max u v} R) (.up ℕ) (.up ℕ) (.up ℕ)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{max u v} R) (.up ℕ) n
  have h := congrArg T.map (ComplexMap.HodgeComplexMap.inclusion e.hom r).symm
  simp only [Functor.map_comp] at h
  have h' := congrArg H.map h
  simp only [Functor.map_comp] at h'
  exact h'

theorem inverse_inclusion (n : ℕ) (r : ℤ) :
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r) (.up ℕ)) n ≫
      (homologyIso R e n).inv =
    (homologyIso R (truncatedIso R e r) n).inv ≫
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) (.up ℕ)) n :=
  IntegralComparison.InverseCoordinateHomology.inverse (homologyIso R (truncatedIso R e r) n) (homologyIso R e n)
    (HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) (.up ℕ)) n)
    (HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r) (.up ℕ)) n)
    (inclusion R e n r)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.NaturalTotalIso.NaturalTotalHodgeIso
