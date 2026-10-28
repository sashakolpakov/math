import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.ResidueDifferentials
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.TermRanks
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.TopCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.ComplexBaseChange

/-! # Residue Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.ResidueCohomology

noncomputable section

/-! Over a field that kills the parameters, the dual Koszul complex has zero differentials and binomial cohomology dimensions. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def homologyIsoTermOfZeroDifferentials
    {V : Type v} [Category.{w} V] [Abelian V]
    {ι : Type*} {c : ComplexShape ι} (C : HomologicalComplex V c)
    (hC : ∀ i j, C.d i j = 0) (i : ι) : C.homology i ≅ C.X i :=
  (C.sc i).asIsoHomologyι (hC i (c.next i)) ≪≫
    (C.sc i).opcyclesIsoX₂ (hC (c.prev i) i)

variable {R : Type u} [CommRing R]

theorem scalarKoszulChainDual_baseChange_d_zero
    (B : Type u) [CommRing B] [Algebra R B]
    (rs : List R) (hrs : ∀ r ∈ rs, algebraMap R B r = 0) :
    ∀ i j, (((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj
      (HilbertConstruction.Finite.FreeDoubleDualComplex.dualModuleComplexSymm (c := .up ℕ) (Regular.ParameterKoszulResolution.scalarKoszulChainComplex rs))).d i j = 0 := by
  let K := Regular.ParameterKoszulResolution.scalarKoszulChainComplex rs
  let F := HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B
  have hfin (i : ℕ) : Module.Finite R (K.X i) :=
    (FiniteTerms.scalarKoszulComplex_finite_free (ModuleCat.of R R) rs (-(i : ℤ))).1
  have hfree (i : ℕ) : Module.Free R (K.X i) :=
    (FiniteTerms.scalarKoszulComplex_finite_free (ModuleCat.of R R) rs (-(i : ℤ))).2
  let E := HilbertConstruction.Dual.ComplexBaseChange.dualModuleComplexSymmBaseChangeIso (c := .up ℕ) B K hfin hfree
  apply ResidueDifferentials.zero_differentials_of_iso E
  intro i j
  have hzero : ((F.mapHomologicalComplex (.down ℕ)).obj K).d j i = 0 :=
    ResidueDifferentials.scalarKoszulComplex_baseChange_d_zero B (ModuleCat.of R R) rs hrs (-(j : ℤ)) (-(i : ℤ))
  change (HilbertConstruction.Module.DualFunctor.moduleDualFunctor B).map ((((F.mapHomologicalComplex (.down ℕ)).obj K).d j i).op) = 0
  rw [hzero, op_zero, Functor.map_zero]

theorem scalarKoszulChainDual_baseChange_homology_finrank [Nontrivial R]
    (B : Type u) [Field B] [Algebra R B]
    (rs : List R) (hrs : ∀ r ∈ rs, algebraMap R B r = 0) (q : ℕ) :
    Module.finrank B ((((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj
      (HilbertConstruction.Finite.FreeDoubleDualComplex.dualModuleComplexSymm (c := .up ℕ) (Regular.ParameterKoszulResolution.scalarKoszulChainComplex rs))).homology q) =
      rs.length.choose q := by
  let K := Regular.ParameterKoszulResolution.scalarKoszulChainComplex rs
  let D := ((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj
    (HilbertConstruction.Finite.FreeDoubleDualComplex.dualModuleComplexSymm (c := .up ℕ) K)
  have : Module.Finite R (K.X q) :=
    (FiniteTerms.scalarKoszulComplex_finite_free (ModuleCat.of R R) rs (-(q : ℤ))).1
  have : Module.Free R (K.X q) :=
    (FiniteTerms.scalarKoszulComplex_finite_free (ModuleCat.of R R) rs (-(q : ℤ))).2
  let E := homologyIsoTermOfZeroDifferentials D
    (scalarKoszulChainDual_baseChange_d_zero B rs hrs) q
  rw [E.toLinearEquiv.finrank_eq]
  change Module.finrank B (B ⊗[R] Module.Dual R (K.X q)) = rs.length.choose q
  rw [(HilbertConstruction.Module.DualBaseChange.moduleDualBaseChangeEquiv B (K.X q)).finrank_eq,
    Subspace.dual_finrank_eq, Module.finrank_baseChange]
  change Module.finrank R ((KoszulComplex.scalarKoszulComplex (ModuleCat.of R R) rs).X (-(q : ℤ))) = _
  simpa only [Module.finrank_self, mul_one] using
    TermRanks.scalarKoszulComplex_term_finrank (ModuleCat.of R R) rs q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.ResidueCohomology
