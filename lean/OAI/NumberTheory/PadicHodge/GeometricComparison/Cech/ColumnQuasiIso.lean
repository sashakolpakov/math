import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.ProductQuasiIso
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits
import OAI.NumberTheory.PadicHodge.IntegralComparison.QuasiIsoFunctorIso

/-! # Column Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.ColumnQuasiIso.CechColumnQuasiIso

noncomputable section

/-! Local quasi-isomorphisms on the actual Cech intersections give
quasi-isomorphisms of every column of the Cech bicomplex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v s t
variable (R : Type u) [CommRing R] {C : Type s} [Category.{t} C]
  (E : SimplicialObject (FormalCoproduct.{0} C))
  {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ} (a : K ⟶ L) (n : ℕ)

local instance limits : HasLimitsOfSize.{0, 0} (ModuleCat.{max u v} R) :=
  ModuleCat.hasLimitsOfSize.{0, 0, max u v, u}

theorem quasiIso (ha : ∀ i : (E.obj (op ⦋n⦌)).I,
    QuasiIso ((((evaluation Cᵒᵖ (ModuleCat.{max u v} R)).obj
      (op ((E.obj (op ⦋n⦌)).obj i))).mapHomologicalComplex (.up ℕ)).map a)) :
    QuasiIso (((FormalCoproduct.cochainComplexFunctor E ⋙
      HomologicalComplex.eval (ModuleCat.{max u v} R) (.up ℕ) n).mapHomologicalComplex (.up ℕ)).map a) := by
  let F := (Functor.whiskeringLeft (Discrete (E.obj (op ⦋n⦌)).I) Cᵒᵖ
    (ModuleCat.{max u v} R)).obj (AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits.CechCochainLimits.indices E n)
  let h : QuasiIso (((AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits.CechCochainLimits.productDegree (A := ModuleCat.{max u v} R) E n).mapHomologicalComplex (.up ℕ)).map a) :=
    Module.ProductQuasiIso.ModuleProductQuasiIso.quasiIso R (E.obj (op ⦋n⦌)).I
      ((F.mapHomologicalComplex (.up ℕ)).map a) (fun i => ha i.as)
  exact IntegralComparison.QuasiIsoFunctorIso.transport _ _
    (NatIso.mapHomologicalComplex (AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits.CechCochainLimits.degreeIso (A := ModuleCat.{max u v} R) E n).symm (.up ℕ)) a

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.ColumnQuasiIso.CechColumnQuasiIso
