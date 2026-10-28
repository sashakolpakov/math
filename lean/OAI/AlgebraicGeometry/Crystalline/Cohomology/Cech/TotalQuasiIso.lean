import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.ColumnQuasiIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalFlip
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMap

/-! # Total Quasi Iso -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso

noncomputable section

/-! Local quasi-isomorphisms on every nerve object induce a quasi-isomorphism of the actual Cech total in all degrees. -/

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
    QuasiIso ((NumberTheory.PadicHodge.GeometricComparison.TotalFlip.TotalFlipNaturality.flipped ((bicomplex R E).map a)).f n) :=
  NumberTheory.PadicHodge.GeometricComparison.Cech.ColumnQuasiIso.CechColumnQuasiIso.quasiIso R E a n ha

theorem quasiIso (ha : ∀ (n : ℕ) (i : (E.obj (op ⦋n⦌)).I),
    QuasiIso ((((evaluation Cᵒᵖ (ModuleCat.{max u v} R)).obj
      (op ((E.obj (op ⦋n⦌)).obj i))).mapHomologicalComplex (.up ℕ)).map a)) :
    QuasiIso (CechTotalQuasiIso.map R E a) := by
  let : QuasiIso (HomologicalComplex₂.total.map
      (NumberTheory.PadicHodge.GeometricComparison.TotalFlip.TotalFlipNaturality.flipped ((bicomplex R E).map a)) (.up ℕ)) :=
    AlgebraicTopology.DeRham.Comparison.DoubleComplexMap.DoubleComplex.total_map_quasiIso_of_columns _ (fun n => column_quasiIso R E a n (ha n))
  apply (_root_.quasiIso_iff _).mpr
  intro n
  exact (NumberTheory.PadicHodge.GeometricComparison.TotalFlip.TotalFlipNaturality.quasiIsoAt_iff ((bicomplex R E).map a) n).mp inferInstance

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso
