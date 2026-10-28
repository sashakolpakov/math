import OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator
import OAI.AlgebraicGeometry.CycleClass.Geometric.SimplexFillings

/-! # Subdivision Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionNaturality

noncomputable section

/-!
# Naturality and normalization of actual subdivision

These are properties of the actual degreewise signed subdivision operator.
No differential commutation or chain homotopy is assumed here.
-/

open _root_.CategoryTheory
open scoped Simplicial BigOperators Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Cycles

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

/-- Any two points of the genuine standard zero-simplex agree. -/
theorem standardZeroSimplex_eq (x y : Convexity.StdSimplex ℝ (Fin 1)) : x = y := by
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 1)).injective
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have hx := Convexity.StdSimplex.total_of_fintype x
  have hy := Convexity.StdSimplex.total_of_fintype y
  simp only [Fin.sum_univ_one] at hx hy
  exact hx.trans hy.symm

/-- Geometric subdivision fixes every zero-simplex. -/
@[simp]
theorem subdivisionSimplex_zero (X : TopCat.{0}) (s : SubdivisionOperator.Cycles.SingularSimplex X 0)
    (σ : Equiv.Perm (Fin 1)) : SubdivisionOperator.Cycles.subdivisionSimplex X 0 s σ = s := by
  apply (X.toSSetObjEquiv (.op ⦋0⦌)).injective
  rw [SubdivisionOperator.Cycles.subdivisionSimplex_toContinuousMap]
  apply ContinuousMap.ext
  intro x
  simp only [ContinuousMap.comp_apply]
  rw [standardZeroSimplex_eq (BarycentricSimplex.Cycles.barycentricSubdivisionMap σ x) x]

/-- The signed generator formula is the identity in degree zero. -/
@[simp]
theorem subdivisionGenerator_zero (X : TopCat.{0}) (s : SubdivisionOperator.Cycles.SingularSimplex X 0) :
    SubdivisionOperator.Cycles.subdivisionGenerator X 0 s = Finsupp.single s 1 := by
  have hsign (σ : Equiv.Perm (Fin 1)) : (Equiv.Perm.sign σ : ℤ) = 1 := by
    rw [show σ = 1 from Subsingleton.elim _ _]
    simp
  simp [SubdivisionOperator.Cycles.subdivisionGenerator, hsign]

/-- The coefficient subdivision map is the identity in degree zero. -/
theorem subdivisionFinsupp_zero_dimension (X : TopCat.{0}) :
    SubdivisionOperator.Cycles.subdivisionFinsupp X 0 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro s a
  simp [SubdivisionOperator.Cycles.subdivisionFinsupp, Finsupp.smul_single]

/-- Actual singular zero-chains are fixed by subdivision. -/
theorem subdivisionDegree_zero_dimension (X : TopCat.{0}) :
    SubdivisionOperator.Cycles.subdivisionDegree X 0 = LinearMap.id := by
  apply LinearMap.ext
  intro c
  apply (SingularChainSupport.Cycles.singularChainCoefficients X 0).injective
  rw [SubdivisionOperator.Cycles.subdivisionDegree_coefficients, subdivisionFinsupp_zero_dimension]
  rfl

@[simp]
theorem subdivisionDegree_zero_dimension_apply (X : TopCat.{0})
    (c : (LocalHomology.Cycles.integralSingularChains X).X 0) : SubdivisionOperator.Cycles.subdivisionDegree X 0 c = c := by
  rw [subdivisionDegree_zero_dimension]
  rfl

/-- Compatibility with the actual canonical zero-chain augmentation. -/
@[simp]
theorem singularZeroChainAugmentation_subdivision (X : TopCat.{0})
    (c : (LocalHomology.Cycles.integralSingularChains X).X 0) :
    SimplexFillings.Cycles.singularZeroChainAugmentation X (SubdivisionOperator.Cycles.subdivisionDegree X 0 c) =
      SimplexFillings.Cycles.singularZeroChainAugmentation X c := by
  rw [subdivisionDegree_zero_dimension_apply]

/-- A barycentric cell commutes with continuous postcomposition. -/
theorem subdivisionSimplex_postcompose {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X n) (σ : Equiv.Perm (Fin (n + 1))) :
    (TopCat.toSSet.map f).app _ (SubdivisionOperator.Cycles.subdivisionSimplex X n s σ) =
      SubdivisionOperator.Cycles.subdivisionSimplex Y n ((TopCat.toSSet.map f).app _ s) σ := by
  have hgeom (t : SubdivisionOperator.Cycles.SingularSimplex X n) :
      Y.toSSetObjEquiv (.op ⦋n⦌) ((TopCat.toSSet.map f).app _ t) =
        f.hom.comp (X.toSSetObjEquiv (.op ⦋n⦌) t) := rfl
  apply (Y.toSSetObjEquiv (.op ⦋n⦌)).injective
  rw [hgeom, SubdivisionOperator.Cycles.subdivisionSimplex_toContinuousMap, SubdivisionOperator.Cycles.subdivisionSimplex_toContinuousMap, hgeom]
  rfl

/-- The actual singular-chain pushforward in an individual degree. -/
abbrev singularChainPostcompose {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    (LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] (LocalHomology.Cycles.integralSingularChains Y).X n :=
  ((LocalHomology.Cycles.integralSingularChainFunctor.map f).f n).hom

/-- Its action on a genuine simplex summand is literal postcomposition. -/
@[simp]
theorem singularChainPostcompose_simplex {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X n) (a : ℤ) :
    singularChainPostcompose f n
      ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s a) =
      (TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of ℤ ℤ)
        ((TopCat.toSSet.map f).app _ s) a := by
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using!
    congrArg (fun g : ModuleCat.of ℤ ℤ ⟶ (LocalHomology.Cycles.integralSingularChains Y).X n => g.hom a)
      (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
        (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ) s)

/-- To check a linear map on actual singular chains, check each simplex summand. -/
theorem singularChainLinearMap_ext (X : TopCat.{0}) (n : ℕ) (M : ModuleCat.{0} ℤ)
    (f g : (LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] M)
    (h : ∀ (s : SubdivisionOperator.Cycles.SingularSimplex X n) (a : ℤ),
      f ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s a) =
      g ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s a)) : f = g := by
  have hcat : ModuleCat.ofHom f = ModuleCat.ofHom g := by
    apply (TopCat.toSSet.obj X).chainComplex_hom_ext
    intro s
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply] using! h s a
  exact congrArg (fun k => k.hom) hcat

/-- Actual degreewise subdivision is natural under any continuous map. -/
theorem subdivisionDegree_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    (singularChainPostcompose f n).comp (SubdivisionOperator.Cycles.subdivisionDegree X n) =
      (SubdivisionOperator.Cycles.subdivisionDegree Y n).comp (singularChainPostcompose f n) := by
  have hsd (Z : TopCat.{0}) (t : SubdivisionOperator.Cycles.SingularSimplex Z n) (b : ℤ) :
      SubdivisionOperator.Cycles.subdivisionDegree Z n ((TopCat.toSSet.obj Z).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) t b) =
        ∑ σ : Equiv.Perm (Fin (n + 1)),
          (TopCat.toSSet.obj Z).ιChainComplex (R := ModuleCat.of ℤ ℤ)
            (SubdivisionOperator.Cycles.subdivisionSimplex Z n t σ) ((Equiv.Perm.sign σ : ℤ) * b) := by
    simpa only using! SubdivisionOperator.Cycles.subdivisionDegree_simplex Z n t b
  have hp (t : SubdivisionOperator.Cycles.SingularSimplex X n) (b : ℤ) :
      singularChainPostcompose f n
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) t b) =
        (TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.map f).app _ t) b := by
    simpa only using! singularChainPostcompose_simplex f n t b
  apply singularChainLinearMap_ext X n ((LocalHomology.Cycles.integralSingularChains Y).X n)
  intro s a
  simp only [LinearMap.comp_apply, hsd, map_sum, hp, subdivisionSimplex_postcompose]

/-- Pointwise naturality, convenient for the actual acyclic-model construction. -/
theorem subdivisionDegree_naturality_apply {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    singularChainPostcompose f n (SubdivisionOperator.Cycles.subdivisionDegree X n c) =
      SubdivisionOperator.Cycles.subdivisionDegree Y n (singularChainPostcompose f n c) :=
  LinearMap.congr_fun (subdivisionDegree_naturality f n) c

/-- Once a chain is subordinate to a cover, subdivision preserves that property.
This uses actual range containment and imposes no openness assumption. -/
theorem subdivisionDegree_preserves_small {X : TopCat.{0}} {J : Type}
    (U : J → Set X) (n : ℕ) (c : (LocalHomology.Cycles.integralSingularChains X).X n)
    (hc : ∀ s ∈ SingularChainSupport.Cycles.singularChainSupport c,
      s ∈ (AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U).obj (.op ⦋n⦌)) :
    ∀ t ∈ SingularChainSupport.Cycles.singularChainSupport (SubdivisionOperator.Cycles.subdivisionDegree X n c),
      t ∈ (AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U).obj (.op ⦋n⦌) := by
  intro t ht
  obtain ⟨s, hs, hsub⟩ := SubdivisionOperator.Cycles.support_subdivisionDegree_range X n c t ht
  obtain ⟨j, hj⟩ := hc s hs
  exact ⟨j, hsub.trans hj⟩

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionNaturality
