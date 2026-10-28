import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.ColumnQuasiIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalOneQuasiIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalFlip

/-! # Total One Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso

noncomputable section

/-! Local comparisons on the actual nerve objects induce an isomorphism on
degree-one homology of the original Cech total complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v s t
variable (R : Type u) [CommRing R] {C : Type s} [Category.{t} C]
  (E : SimplicialObject (FormalCoproduct.{0} C))

local instance limits : HasLimitsOfSize.{0, 0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasLimitsOfSize.{0, 0, max u v, u}

local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasColimitsOfSize.{max u v, u, 0, 0} R

def bicomplex : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ ⥤
    HomologicalComplex₂ (ModuleCat.{max u v} R) (.up ℕ) (.up ℕ) :=
  (FormalCoproduct.cochainComplexFunctor E).mapHomologicalComplex (.up ℕ)

variable {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ} (a : K ⟶ L)

def map : ((bicomplex R E).obj K).total (.up ℕ) ⟶ ((bicomplex R E).obj L).total (.up ℕ) :=
  HomologicalComplex₂.total.map ((bicomplex R E).map a) (.up ℕ)

theorem column_quasiIso (n : ℕ) (ha : ∀ i : (E.obj (op ⦋n⦌)).I,
    QuasiIso ((((evaluation Cᵒᵖ (ModuleCat.{max u v} R)).obj
      (op ((E.obj (op ⦋n⦌)).obj i))).mapHomologicalComplex (.up ℕ)).map a)) :
    QuasiIso ((TotalFlip.TotalFlipNaturality.flipped ((bicomplex R E).map a)).f n) :=
  ColumnQuasiIso.CechColumnQuasiIso.quasiIso R E a n ha

theorem quasiIsoAt (ha : ∀ (n : ℕ) (i : (E.obj (op ⦋n⦌)).I),
    QuasiIso ((((evaluation Cᵒᵖ (ModuleCat.{max u v} R)).obj
      (op ((E.obj (op ⦋n⦌)).obj i))).mapHomologicalComplex (.up ℕ)).map a)) :
    QuasiIsoAt (CechTotalHOneQuasiIso.map R E a) 1 := by
  let h2 : QuasiIso ((TotalFlip.TotalFlipNaturality.flipped ((bicomplex R E).map a)).f 2) :=
    column_quasiIso R E a 2 (ha 2)
  exact (TotalFlip.TotalFlipNaturality.quasiIsoAt_iff ((bicomplex R E).map a) 1).mp
    (Module.TotalOneQuasiIso.ModuleTotalHOneQuasiIso.quasiIsoAt _ (column_quasiIso R E a 0 (ha 0))
      (column_quasiIso R E a 1 (ha 1)) inferInstance)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso
