import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.TotalQuasiIso
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexMap
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence

/-! # Total Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.TotalQuasiIso

noncomputable section

/-! Rowwise quasi-isomorphisms induce a quasi-isomorphism on the original
nonnegative additive total complex. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

universe u
local instance : (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv.Additive := by
  let : (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.functor.Additive := by
    change (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).Additive
    infer_instance
  exact (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.inverse_additive
local instance : HasFiniteBiproducts AddCommGrpCat.{u} :=
  HasFiniteBiproducts.of_hasFiniteProducts
variable {K L : HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ)}
  (g : K ⟶ L)

theorem quasiIso (hg : ∀ q, QuasiIso (g.f q)) :
    QuasiIso (total.map g (.up ℕ)) := by
  let F := (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv
  let : ∀ q, QuasiIso (g.f q) := hg
  let : QuasiIso (total.map (AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap F g) (.up ℕ)) :=
    AlgebraicTopology.DeRham.Comparison.DoubleComplexMap.DoubleComplex.total_map_quasiIso_of_columns _ (fun q => by
      change QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map (g.f q))
      infer_instance)
  let e := AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso F K
  let d := AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso F L
  have h := AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.totalComparison_naturality F g
  have hc : QuasiIso (e.hom ≫ (F.mapHomologicalComplex (.up ℕ)).map
      (total.map g (.up ℕ))) := by
    change QuasiIso (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparison F K ≫ _)
    rw [← h]
    change QuasiIso (_ ≫ d.hom)
    infer_instance
  have : QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map (total.map g (.up ℕ))) :=
    quasiIso_of_comp_left e.hom _ (hφφ' := hc)
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ F).mp this

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.TotalQuasiIso
