import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallChainImage
import OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy

/-! # Natural Small Chains -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.NaturalSmallChains

noncomputable section

/-!
# Natural chain operations preserve small singular chains

A singular simplex whose image lies in a subset factors continuously through
that subset. Naturality therefore forces every natural operation on singular
chains to carry this simplex into the image of the same subspace. Taking sums
shows that the actual image of the small-chain inclusion is preserved.

The argument works for any family of subsets; openness and the covering
condition are unnecessary for this locality statement.
-/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

open _root_.CategoryTheory
open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A simplex with image in a subset is an actual simplex of the subspace. -/
theorem singularSimplex_liftsToSubspace (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (s : (TopCat.toSSet.obj X).obj (.op ⦋n⦌))
    (hs : Set.range (X.toSSetObjEquiv (.op ⦋n⦌) s) ⊆ A) :
    ∃ t : (TopCat.toSSet.obj (TopCat.of A)).obj (.op ⦋n⦌),
      (TopCat.toSSet.map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A)).app (.op ⦋n⦌) t = s := by
  let g := X.toSSetObjEquiv (.op ⦋n⦌) s
  let h : C(Convexity.StdSimplex ℝ (Fin (n + 1)), A) :=
    ⟨fun x => ⟨g x, hs ⟨x, rfl⟩⟩, g.continuous.subtype_mk _⟩
  refine ⟨((TopCat.of A).toSSetObjEquiv (.op ⦋n⦌)).symm h, ?_⟩
  apply (X.toSSetObjEquiv (.op ⦋n⦌)).injective
  change (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A).hom.comp
    ((TopCat.of A).toSSetObjEquiv (.op ⦋n⦌)
      (((TopCat.of A).toSSetObjEquiv (.op ⦋n⦌)).symm h)) = g
  rw [Equiv.apply_symm_apply]
  rfl

variable (X : TopCat.{0}) {J : Type} (U : J → Set X)

/-- Singular simplices of a family member give small singular simplices. -/
def coverMemberSingularMap (i : J) :
    TopCat.toSSet.obj (TopCat.of (U i)) ⟶
      (DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet) :=
  SSet.Subcomplex.lift (TopCat.toSSet.map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (U i))) (by
    intro n s hs
    obtain ⟨t, rfl⟩ := hs
    refine ⟨i, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (((TopCat.of (U i)).toSSetObjEquiv n t) x).property)

@[reassoc (attr := simp)]
theorem coverMemberSingularMap_inclusion (i : J) :
    coverMemberSingularMap X U i ≫ DeRham.Comparison.SmallSingularSet.smallSingularInclusion X U =
      TopCat.toSSet.map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (U i)) := rfl

/-- The subspace chain map factors through the genuine small-chain complex. -/
def coverMemberChainMap (i : J) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (U i)) ⟶ AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.integralSmallSingularChains X U :=
  SSet.chainComplexMap (coverMemberSingularMap X U i) (ModuleCat.of ℤ ℤ)

@[reassoc (attr := simp)]
theorem coverMemberChainMap_inclusion (i : J) :
    coverMemberChainMap X U i ≫ AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X U =
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X (U i) := by
  change ((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map
      (coverMemberSingularMap X U i) ≫
    ((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map
      (DeRham.Comparison.SmallSingularSet.smallSingularInclusion X U) = _
  rw [← Functor.map_comp, coverMemberSingularMap_inclusion]
  rfl

/-- Any natural chain operation sends a small simplex summand into the actual
image of the small-chain inclusion. -/
theorem naturalSingularOperation_smallSimplex {n m : ℕ}
    (a : AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy.Cycles.singularChainDegreeFunctor n ⟶ AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy.Cycles.singularChainDegreeFunctor m)
    (s : (TopCat.toSSet.obj X).obj (.op ⦋n⦌))
    (hs : s ∈ (DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U).obj (.op ⦋n⦌))
    (z : ℤ) :
    a.app X ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s z) ∈
      LinearMap.range ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X U).f m).hom := by
  obtain ⟨i, hi⟩ := hs
  obtain ⟨t, ht⟩ := singularSimplex_liftsToSubspace X (U i) n s hi
  let u := (TopCat.toSSet.obj (TopCat.of (U i))).ιChainComplex
    (R := ModuleCat.of ℤ ℤ) t z
  have hu : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X (U i)).f n u =
      (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s z := by
    change AlgebraicGeometry.CycleClass.Geometric.SubdivisionNaturality.Cycles.singularChainPostcompose (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (U i)) n
      ((TopCat.toSSet.obj (TopCat.of (U i))).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) t z) = _
    rw [AlgebraicGeometry.CycleClass.Geometric.SubdivisionNaturality.Cycles.singularChainPostcompose_simplex, ht]
  have hnat : a.app X ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X (U i)).f n u) =
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X (U i)).f m (a.app (TopCat.of (U i)) u) := by
    exact ConcreteCategory.congr_hom (a.naturality (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (U i))) u
  rw [hu] at hnat
  refine ⟨(coverMemberChainMap X U i).f m (a.app (TopCat.of (U i)) u), ?_⟩
  rw [hnat]
  exact ConcreteCategory.congr_hom
    (congrArg (fun f => f.f m) (coverMemberChainMap_inclusion X U i))
    (a.app (TopCat.of (U i)) u)

/-- Every natural operation on ordinary integral singular chains preserves the
actual image of the small-chain inclusion, for an arbitrary family of subsets. -/
theorem naturalSingularOperation_preserves_smallChainImage {n m : ℕ}
    (a : AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy.Cycles.singularChainDegreeFunctor n ⟶ AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy.Cycles.singularChainDegreeFunctor m)
    (X : TopCat.{0}) {J : Type} (U : J → Set X)
    {c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n}
    (hc : c ∈ LinearMap.range ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom) :
    a.app X c ∈ LinearMap.range ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X U).f m).hom := by
  let P := LinearMap.range ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X U).f m).hom
  let : Module ℤ ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X m ⧸ P) := Submodule.Quotient.module P
  have hzero : (AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n ≫ a.app X ≫
      ModuleCat.ofHom P.mkQ = 0 := by
    apply SSet.chainComplex_hom_ext
    intro s
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    have hsmall := naturalSingularOperation_smallSimplex X U a s.val s.property z
    have hgen : (AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n
        ((DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) s z) =
        (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s.val z :=
      ConcreteCategory.congr_hom
        (SSet.ι_chainComplexMap_f
          (DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet)
          (TopCat.toSSet.obj X) (DeRham.Comparison.SmallSingularSet.smallSingularInclusion X U)
          (ModuleCat.of ℤ ℤ) s) z
    change P.mkQ (a.app X ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n
      ((DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) s z))) = 0
    rw [hgen, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hsmall
  obtain ⟨b, rfl⟩ := hc
  have hb := ConcreteCategory.congr_hom hzero b
  change P.mkQ (a.app X ((AlgebraicGeometry.CycleClass.Geometric.SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n b)) = 0 at hb
  exact (Submodule.Quotient.mk_eq_zero (p := P)).mp hb

end

end OAI.AlgebraicTopology.Cohomology.Singular.NaturalSmallChains
