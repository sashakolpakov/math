import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalOneQuasiIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.TruncatedFunctorIso
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor

/-! # Total Truncation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalTruncation.CechTotalHodgeTruncation

noncomputable section

/-! Truncating form degree before Cech cochains agrees with the actual
outer-degree truncation of the Cech bicomplex, including its inclusion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Simplicial

universe u v s t
variable (R : Type u) [CommRing R] {C : Type s} [Category.{t} C]
  (E : SimplicialObject (FormalCoproduct.{0} C))
  (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ) (r : ℤ)

local instance limits : HasLimitsOfSize.{0, 0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasLimitsOfSize.{0, 0, max u v, u}

local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasColimitsOfSize.{max u v, u, 0, 0} R

def bicomplexIso : (TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{u, v} R E).obj (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r) ≅
    AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal ((TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{u, v} R E).obj K) r :=
  TruncatedFunctorIso.TruncatedPullback.iso (FormalCoproduct.cochainComplexFunctor E) (Iso.refl _) r

def totalIso : ((TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{u, v} R E).obj (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r)).total (.up ℕ) ≅
    HomologicalComplex₂.total
      (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal ((TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{u, v} R E).obj K) r) (.up ℕ) :=
  HomologicalComplex₂.total.mapIso (bicomplexIso.{u, v} R E K r) (.up ℕ)

theorem inclusion : (totalIso.{u, v} R E K r).hom ≫
    HomologicalComplex₂.total.map
      (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion ((TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{u, v} R E).obj K) r) (.up ℕ) =
    TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{u, v} R E (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) := by
  have h := TruncatedFunctorIso.TruncatedPullback.iso_inclusion (FormalCoproduct.cochainComplexFunctor E)
    (Iso.refl ((TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{u, v} R E).obj K)) r
  have h' := h.trans (Category.comp_id _)
  let T := HomologicalComplex₂.totalFunctor (ModuleCat.{max u v} R) (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp _ _).symm.trans (congrArg T.map h')

theorem inverse_inclusion :
    HomologicalComplex₂.total.map
      (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion ((TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{u, v} R E).obj K) r) (.up ℕ) =
    (totalIso.{u, v} R E K r).inv ≫ TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{u, v} R E (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K r) :=
  ((totalIso.{u, v} R E K r).inv_comp_eq.mpr (inclusion.{u, v} R E K r).symm).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalTruncation.CechTotalHodgeTruncation
