import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallChainImage
import OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionBoundary
import OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionNaturality

/-! # Subcomplex Subdivision -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SubcomplexSubdivision

noncomputable section

/-!
# Barycentric subdivision on an invariant singular subcomplex

If the actual cells of barycentric subdivision belong to a singular
subcomplex, their signed sum gives an operator on its genuine integral chains.
The inclusion carries it to the existing ordinary subdivision operator.
Injectivity of the inclusion then proves boundary compatibility.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial BigOperators

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{0}) (S : (TopCat.toSSet.obj X).Subcomplex)

/-- Actual integral chains of a singular simplicial subcomplex. -/
abbrev subcomplexIntegralChains : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  S.toSSet.chainComplex (ModuleCat.of ℤ ℤ)

/-- The actual inclusion of subcomplex chains into ordinary singular chains. -/
abbrev subcomplexIntegralChainInclusion :
    subcomplexIntegralChains X S ⟶ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X :=
  SSet.chainComplexMap S.ι (ModuleCat.of ℤ ℤ)

/-- The integral chain inclusion is injective in every degree. -/
theorem subcomplexIntegralChainInclusion_injective (n : ℕ) :
    Function.Injective ((subcomplexIntegralChainInclusion X S).f n) := by
  intro a b hab
  apply (AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.simplicialIntegralChainCoefficients S.toSSet n).injective
  apply Finsupp.mapDomain_injective Subtype.val_injective
  have h := congrArg (AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.simplicialIntegralChainCoefficients (TopCat.toSSet.obj X) n) hab
  exact (AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.simplicialIntegralChainCoefficients_map S.ι n a).symm.trans
    (h.trans (AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.simplicialIntegralChainCoefficients_map S.ι n b))

/-- A simplex generator is carried to precisely its underlying singular simplex. -/
@[simp]
theorem subcomplexIntegralChainInclusion_simplex {n : ℕ}
    (s : S.toSSet _⦋n⦌) (a : ℤ) :
    (subcomplexIntegralChainInclusion X S).f n
        (S.toSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) s a) =
      (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s.val a :=
  ConcreteCategory.congr_hom
    (SSet.ι_chainComplexMap_f S.toSSet (TopCat.toSSet.obj X) S.ι (ModuleCat.of ℤ ℤ) s) a

/-- Elementwise boundary compatibility of the actual inclusion. -/
theorem subcomplexIntegralChainInclusion_d (i j : ℕ)
    (c : (subcomplexIntegralChains X S).X i) :
    (subcomplexIntegralChainInclusion X S).f j ((subcomplexIntegralChains X S).d i j c) =
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d i j ((subcomplexIntegralChainInclusion X S).f i c) :=
  (ConcreteCategory.congr_hom ((subcomplexIntegralChainInclusion X S).comm i j) c).symm

variable (hS : ∀ {n : ℕ} (s : S.toSSet _⦋n⦌) (σ : Equiv.Perm (Fin (n + 1))),
  AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator.Cycles.subdivisionSimplex X n s.val σ ∈ S.obj (.op ⦋n⦌))

/-- A specific ordinary barycentric cell, with its proved subcomplex membership. -/
def subcomplexSubdivisionSimplex {n : ℕ} (s : S.toSSet _⦋n⦌)
    (σ : Equiv.Perm (Fin (n + 1))) : S.toSSet _⦋n⦌ :=
  ⟨AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator.Cycles.subdivisionSimplex X n s.val σ, hS s σ⟩

/-- The signed barycentric cell sum extended linearly from actual simplex generators. -/
def subcomplexSubdivisionDegree (n : ℕ) :
    (subcomplexIntegralChains X S).X n →ₗ[ℤ] (subcomplexIntegralChains X S).X n :=
  ChainDual.chainFunctionalOfFunction S.toSSet ((subcomplexIntegralChains X S).X n) n
    (fun s => ∑ σ : Equiv.Perm (Fin (n + 1)),
      S.toSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ)
        (subcomplexSubdivisionSimplex X S hS s σ) (Equiv.Perm.sign σ : ℤ))

/-- The restricted operator has exactly the usual signed barycentric-cell formula. -/
@[simp]
theorem subcomplexSubdivisionDegree_simplex {n : ℕ} (s : S.toSSet _⦋n⦌) :
    subcomplexSubdivisionDegree X S hS n
        (S.toSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) s 1) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), S.toSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ)
        (subcomplexSubdivisionSimplex X S hS s σ) (Equiv.Perm.sign σ : ℤ) :=
  ChainDual.chainFunctionalOfFunction_simplex S.toSSet ((subcomplexIntegralChains X S).X n) n _ s

/-- The restricted operator is precisely ordinary subdivision under inclusion. -/
theorem subcomplexSubdivisionDegree_intertwining (n : ℕ) :
    ((subcomplexIntegralChainInclusion X S).f n).hom.comp
        (subcomplexSubdivisionDegree X S hS n) =
      (AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator.Cycles.subdivisionDegree X n).comp ((subcomplexIntegralChainInclusion X S).f n).hom := by
  apply ChainDual.chainFunctional_ext S.toSSet ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n)
  intro s
  change (subcomplexIntegralChainInclusion X S).f n
      (subcomplexSubdivisionDegree X S hS n
        (S.toSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) s 1)) =
    AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator.Cycles.subdivisionDegree X n ((subcomplexIntegralChainInclusion X S).f n
      (S.toSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ) s 1))
  calc
    _ = (subcomplexIntegralChainInclusion X S).f n
        (∑ σ : Equiv.Perm (Fin (n + 1)), S.toSSet.ιChainComplex
          (R := ModuleCat.of ℤ ℤ) (subcomplexSubdivisionSimplex X S hS s σ)
            (Equiv.Perm.sign σ : ℤ)) :=
      congrArg ((subcomplexIntegralChainInclusion X S).f n)
        (subcomplexSubdivisionDegree_simplex X S hS s)
    _ = ∑ σ : Equiv.Perm (Fin (n + 1)), (subcomplexIntegralChainInclusion X S).f n
        (S.toSSet.ιChainComplex (R := ModuleCat.of ℤ ℤ)
          (subcomplexSubdivisionSimplex X S hS s σ) (Equiv.Perm.sign σ : ℤ)) :=
      map_sum ((subcomplexIntegralChainInclusion X S).f n).hom _ _
    _ = ∑ σ : Equiv.Perm (Fin (n + 1)), (TopCat.toSSet.obj X).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) (AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator.Cycles.subdivisionSimplex X n s.val σ)
          (Equiv.Perm.sign σ : ℤ) := by
      apply Finset.sum_congr rfl
      intro σ _
      exact subcomplexIntegralChainInclusion_simplex X S
        (subcomplexSubdivisionSimplex X S hS s σ) _
    _ = AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator.Cycles.subdivisionDegree X n
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s.val 1) := by
      simpa only [mul_one] using (AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator.Cycles.subdivisionDegree_simplex X n s.val 1).symm
    _ = _ := congrArg (AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator.Cycles.subdivisionDegree X n)
      (subcomplexIntegralChainInclusion_simplex X S s 1).symm

@[simp]
theorem subcomplexSubdivisionDegree_inclusion (n : ℕ)
    (c : (subcomplexIntegralChains X S).X n) :
    (subcomplexIntegralChainInclusion X S).f n (subcomplexSubdivisionDegree X S hS n c) =
      AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator.Cycles.subdivisionDegree X n ((subcomplexIntegralChainInclusion X S).f n c) :=
  LinearMap.congr_fun (subcomplexSubdivisionDegree_intertwining X S hS n) c

/-- No new boundary calculation is assumed: injectivity reduces it to the
proved boundary identity for ordinary barycentric subdivision. -/
theorem subcomplexSubdivisionDegree_boundary (n : ℕ)
    (c : (subcomplexIntegralChains X S).X (n + 1)) :
    (subcomplexIntegralChains X S).d (n + 1) n
        (subcomplexSubdivisionDegree X S hS (n + 1) c) =
      subcomplexSubdivisionDegree X S hS n ((subcomplexIntegralChains X S).d (n + 1) n c) := by
  apply subcomplexIntegralChainInclusion_injective X S n
  simpa only [subcomplexIntegralChainInclusion_d, subcomplexSubdivisionDegree_inclusion] using
    AlgebraicGeometry.CycleClass.Geometric.SubdivisionBoundary.Cycles.subdivisionDegree_boundary X n ((subcomplexIntegralChainInclusion X S).f (n + 1) c)

/-- Barycentric subdivision on the actual invariant subcomplex chains. -/
def subcomplexSubdivisionChainMap :
    subcomplexIntegralChains X S ⟶ subcomplexIntegralChains X S :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (subcomplexSubdivisionDegree X S hS n))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact subcomplexSubdivisionDegree_boundary X S hS n c)

@[simp]
theorem subcomplexSubdivisionChainMap_f (n : ℕ) :
    ((subcomplexSubdivisionChainMap X S hS).f n).hom = subcomplexSubdivisionDegree X S hS n := rfl

/-- Actual chain-map inclusion compatibility. -/
theorem subcomplexSubdivisionChainMap_intertwining :
    subcomplexIntegralChainInclusion X S ≫ AlgebraicGeometry.CycleClass.Geometric.SubdivisionBoundary.Cycles.subdivisionChainMap X =
      subcomplexSubdivisionChainMap X S hS ≫ subcomplexIntegralChainInclusion X S := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  exact (subcomplexSubdivisionDegree_intertwining X S hS n).symm

/-- The restricted operator fixes degree zero, because ordinary subdivision does. -/
theorem subcomplexSubdivisionDegree_zero_dimension :
    subcomplexSubdivisionDegree X S hS 0 = LinearMap.id := by
  apply LinearMap.ext
  intro c
  apply subcomplexIntegralChainInclusion_injective X S 0
  rw [subcomplexSubdivisionDegree_inclusion, AlgebraicGeometry.CycleClass.Geometric.SubdivisionNaturality.Cycles.subdivisionDegree_zero_dimension_apply]
  rfl

@[simp]
theorem subcomplexSubdivisionChainMap_f_zero :
    (subcomplexSubdivisionChainMap X S hS).f 0 = 𝟙 _ := by
  apply ModuleCat.hom_ext
  exact subcomplexSubdivisionDegree_zero_dimension X S hS

end

end OAI.AlgebraicTopology.Cohomology.Singular.SubcomplexSubdivision
