import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison
import OAI.AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor
import Mathlib.Algebra.Homology.QuasiIso

/-! # Total Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.TotalQuasiIso

noncomputable section

/-! An exact additive coefficient functor preserves a quasi-isomorphism
of the actual nonnegative bicomplex totals. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasCoproducts.{0} C] [HasCoproducts.{0} D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
  {K L : HomologicalComplex₂ C (.up ℕ) (.up ℕ)} (g : K ⟶ L)
  [QuasiIso (total.map g (.up ℕ))]

theorem quasiIso : QuasiIso (total.map (AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap F g) (.up ℕ)) := by
  let : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts
  let e := AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso F K
  let d := AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso F L
  have h := AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.totalComparison_naturality F g
  have hc : QuasiIso (total.map (AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap F g) (.up ℕ) ≫ d.hom) := by
    rw [show d.hom = AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparison F L from rfl, h]
    exact quasiIso_comp e.hom
      ((F.mapHomologicalComplex (.up ℕ)).map (total.map g (.up ℕ)))
  exact quasiIso_of_comp_right _ d.hom (hφφ' := hc)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.TotalQuasiIso
