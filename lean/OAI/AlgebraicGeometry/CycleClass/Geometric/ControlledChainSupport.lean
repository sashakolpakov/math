import OAI.AlgebraicTopology.Cohomology.Singular.NaturalSmallChains
import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Controlled Chain Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ControlledChainSupport.Cycles

noncomputable section

/-!
# Support control for operations on actual singular chains

Support in a subset means membership in the image of the genuine subspace
chain inclusion. The free singular-simplex coefficient description allows
generatorwise support proofs to extend to all chains.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual image of the chains on a subspace in one ambient degree. -/
abbrev singularSubspaceImage (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    Submodule ℤ ((LocalHomology.Cycles.integralSingularChains X).X n) :=
  LinearMap.range ((LocalHomology.Cycles.subspaceChainInclusion X A).f n).hom

/-- Boundaries of chains on a subspace remain chains on that subspace. -/
theorem singularSubspaceImage_boundary (X : TopCat.{0}) (A : Set X) (i j : ℕ)
    {c : (LocalHomology.Cycles.integralSingularChains X).X i} (hc : c ∈ singularSubspaceImage X A i) :
    (LocalHomology.Cycles.integralSingularChains X).d i j c ∈ singularSubspaceImage X A j := by
  obtain ⟨b, rfl⟩ := hc
  refine ⟨(LocalHomology.Cycles.integralSingularChains (TopCat.of A)).d i j b, ?_⟩
  exact (ConcreteCategory.congr_hom ((LocalHomology.Cycles.subspaceChainInclusion X A).comm i j) b).symm

/-- Enlarging a subset enlarges the actual subspace-chain image. -/
theorem singularSubspaceImage_mono (X : TopCat.{0}) {A B : Set X}
    (hAB : A ⊆ B) (n : ℕ) : singularSubspaceImage X A n ≤ singularSubspaceImage X B n := by
  rintro c ⟨b, rfl⟩
  refine ⟨(LocalHomology.Cycles.integralSingularChainFunctor.map (SmallMayerVietoris.Cycles.subsetInclusion X hAB)).f n b, ?_⟩
  have hmap : LocalHomology.Cycles.integralSingularChainFunctor.map (SmallMayerVietoris.Cycles.subsetInclusion X hAB) ≫
      LocalHomology.Cycles.subspaceChainInclusion X B = LocalHomology.Cycles.subspaceChainInclusion X A := by
    change LocalHomology.Cycles.integralSingularChainFunctor.map _ ≫ LocalHomology.Cycles.integralSingularChainFunctor.map _ = _
    rw [← Functor.map_comp]
    rfl
  exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hmap n) b

/-- A simplex whose geometric image lies in A really is a chain on A. -/
theorem singularSimplex_mem_subspaceImage (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌))
    (hσ : Set.range (X.toSSetObjEquiv (.op ⦋n⦌) σ) ⊆ A) (z : ℤ) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ z ∈
      singularSubspaceImage X A n := by
  obtain ⟨τ, hτ⟩ := AlgebraicTopology.Cohomology.Singular.NaturalSmallChains.singularSimplex_liftsToSubspace X A n σ hσ
  refine ⟨(TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
    (R := ModuleCat.of ℤ ℤ) τ z, ?_⟩
  change SubdivisionNaturality.Cycles.singularChainPostcompose (LocalHomology.Cycles.subspaceInclusion X A) n _ = _
  rw [SubdivisionNaturality.Cycles.singularChainPostcompose_simplex, hτ]

/-- Extend specified values on genuine singular simplices by linearity. -/
def singularLinearExtension (X : TopCat.{0}) (n : ℕ) (M : ModuleCat.{0} ℤ)
    (v : (TopCat.toSSet.obj X).obj (.op ⦋n⦌) → M) :
    (LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] M :=
  (Finsupp.linearCombination ℤ v).comp (SingularChainSupport.Cycles.singularChainCoefficients X n).toLinearMap

@[simp]
theorem singularLinearExtension_simplex (X : TopCat.{0}) (n : ℕ) (M : ModuleCat.{0} ℤ)
    (v : (TopCat.toSSet.obj X).obj (.op ⦋n⦌) → M)
    (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) (z : ℤ) :
    singularLinearExtension X n M v
      ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ z) = z • v σ := by
  have h := congrArg (Finsupp.linearCombination ℤ v)
    (SingularChainSupport.Cycles.singularChainCoefficients_simplex_apply X n σ z)
  simp only [Finsupp.linearCombination_single] at h
  exact h.trans (int_smul_eq_zsmul (inferInstance : Module ℤ M) z (v σ))

/-- To prove a linear singular-chain operation lands in a submodule, it
suffices to check the genuine simplex summands. -/
theorem singularLinearMap_mem (X : TopCat.{0}) (n : ℕ) (M : ModuleCat.{0} ℤ)
    (P : Submodule ℤ M) (F : (LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] M)
    (hF : ∀ (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) (z : ℤ),
      F ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ z) ∈ P)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) : F c ∈ P := by
  let : Module ℤ (M ⧸ P) := Submodule.Quotient.module P
  have hz : P.mkQ.comp F = 0 := by
    apply SubdivisionNaturality.Cycles.singularChainLinearMap_ext X n (ModuleCat.of ℤ (M ⧸ P))
    intro σ z
    change P.mkQ (F ((TopCat.toSSet.obj X).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) σ z)) = 0
    exact (Submodule.Quotient.mk_eq_zero P).mpr (hF σ z)
  exact (Submodule.Quotient.mk_eq_zero P).mp (LinearMap.congr_fun hz c)

/-- Over the integers it suffices to check coefficient one on each simplex. -/
theorem singularLinearMap_mem_one (X : TopCat.{0}) (n : ℕ) (M : ModuleCat.{0} ℤ)
    (P : Submodule ℤ M) (F : (LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] M)
    (hF : ∀ σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌),
      F ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ 1) ∈ P)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n) : F c ∈ P := by
  apply singularLinearMap_mem X n M P F _ c
  intro σ z
  have hgen : (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ z =
      z • (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ 1 := by
    simpa only [zsmul_eq_mul, mul_one, Int.cast_id] using!
      (map_zsmul ((TopCat.toSSet.obj X).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) σ).hom z (1 : ℤ))
  rw [hgen, map_zsmul]
  exact P.toAddSubgroup.zsmul_mem (hF σ) z

/-- A generatorwise subspace-support proof extends to all chains on that subspace. -/
theorem singularLinearMap_subspace (X : TopCat.{0}) (A : Set X) (n m : ℕ)
    (F : (LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] (LocalHomology.Cycles.integralSingularChains X).X m)
    (hF : ∀ (σ : (TopCat.toSSet.obj X).obj (.op ⦋n⦌)) (z : ℤ),
      Set.range (X.toSSetObjEquiv (.op ⦋n⦌) σ) ⊆ A →
      F ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ z) ∈
        singularSubspaceImage X A m)
    {c : (LocalHomology.Cycles.integralSingularChains X).X n} (hc : c ∈ singularSubspaceImage X A n) :
    F c ∈ singularSubspaceImage X A m := by
  obtain ⟨b, rfl⟩ := hc
  apply singularLinearMap_mem (TopCat.of A) n ((LocalHomology.Cycles.integralSingularChains X).X m)
    (singularSubspaceImage X A m)
    (F.comp ((LocalHomology.Cycles.subspaceChainInclusion X A).f n).hom) _ b
  intro σ z
  change F (SubdivisionNaturality.Cycles.singularChainPostcompose (LocalHomology.Cycles.subspaceInclusion X A) n _) ∈ _
  rw [SubdivisionNaturality.Cycles.singularChainPostcompose_simplex]
  apply hF
  rintro x ⟨y, rfl⟩
  exact (((TopCat.of A).toSSetObjEquiv (.op ⦋n⦌) σ) y).property

/-- Spatially controlled values on generators give an operation preserving
the image of every actual subspace chain complex. -/
theorem singularLinearExtension_subspace (X : TopCat.{0}) (n m : ℕ)
    (v : (TopCat.toSSet.obj X).obj (.op ⦋n⦌) → (LocalHomology.Cycles.integralSingularChains X).X m)
    (hv : ∀ σ, v σ ∈ singularSubspaceImage X
      (Set.range (X.toSSetObjEquiv (.op ⦋n⦌) σ)) m)
    (A : Set X) {c : (LocalHomology.Cycles.integralSingularChains X).X n}
    (hc : c ∈ singularSubspaceImage X A n) :
    singularLinearExtension X n ((LocalHomology.Cycles.integralSingularChains X).X m) v c ∈
      singularSubspaceImage X A m := by
  apply singularLinearMap_subspace X A n m _ _ hc
  intro σ z hσ
  rw [singularLinearExtension_simplex]
  exact (singularSubspaceImage X A m).toAddSubgroup.zsmul_mem
    (singularSubspaceImage_mono X hσ m (hv σ)) z

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ControlledChainSupport.Cycles
