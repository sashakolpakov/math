import OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularCochains
import OAI.AlgebraicTopology.Cohomology.Singular.Representatives
import OAI.AlgebraicTopology.Cohomology.Singular.Formulas
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Small Cochain Cech -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SmallCochainCech

noncomputable section

/-!
# Čech descent for cover-small singular cochains

The split augmented Čech nerve from `Comparison.CechCoverRows` is evaluated
in the opposite category of coefficient modules. This gives the actual
cochain row, with all functions on Čech simplices, and proves exactness in
positive Čech degrees. Its zeroth cohomology is the module of functions on
the covered set.

For the cover of small singular simplices by the sets of simplices lying
in each spatial cover member, this identifies zeroth row cohomology with
the existing small singular cochain object. Compatible local functions
also glue through an explicit linear equivalence. No comparison between
small and unrestricted singular cochains is used.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

variable {R : Type} [Ring R] {α ι : Type}

/-- The Čech cochain row of a family of subsets of a set. -/
abbrev coverCechCochains (M : ModuleCat.{0} R) (U : ι → Set α) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  Basic.simplicialCochains (DeRham.Comparison.CechCoverRows.coverCechNerve U).left M

/-- The already proved split-nerve contraction, now evaluated in the
opposite module category so that coproducts become cochain products. -/
def coverCechOppositeHomotopyEquiv (M : ModuleCat.{0} R) (U : ι → Set α)
    (hU : ∀ x, ∃ i, x ∈ U i) :
    HomotopyEquiv (SSet.chainComplex (DeRham.Comparison.CechCoverRows.coverCechNerve U).left (op M))
      ((ChainComplex.single₀ (ModuleCat.{0} R)ᵒᵖ).obj
        ((sigmaConst.obj (op M)).obj α)) :=
  ((DeRham.Comparison.CechCoverRows.coverCechExtraDegeneracy U hU).map
    (sigmaConst.obj (op M))).homotopyEquiv

/-- Positive Čech cohomological degrees are exact for the actual row. -/
theorem coverCechCochains_exactAt_succ (M : ModuleCat.{0} R) (U : ι → Set α)
    (hU : ∀ x, ∃ i, x ∈ U i) (k : ℕ) :
    (coverCechCochains M U).ExactAt (k + 1) := by
  apply HomologicalComplex.ExactAt.unop
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact IsZero.of_iso
    (ChainComplex.exactAt_succ_single_obj ((sigmaConst.obj (op M)).obj α) k).isZero_homology
    ((coverCechOppositeHomotopyEquiv M U hU).toHomologyIso (k + 1))

/-- Zeroth cohomology of the Čech row consists of all functions on the
covered set. -/
def coverCechCochainsHomologyZeroIso (M : ModuleCat.{0} R) (U : ι → Set α)
    (hU : ∀ x, ∃ i, x ∈ U i) :
    (coverCechCochains M U).homology 0 ≅ ModuleCat.of R (α → M) :=
  (SSet.chainComplex (DeRham.Comparison.CechCoverRows.coverCechNerve U).left (op M)).homologyUnop 0 ≪≫
    (((coverCechOppositeHomotopyEquiv M U hU).toHomologyIso 0) ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.down ℕ) 0
        ((sigmaConst.obj (op M)).obj α)).unop.symm ≪≫
    (opProductIsoCoproduct (fun _ : α => M)).unop ≪≫
    ModuleCat.piIsoPi (fun _ : α => M)

/-- Every positive-degree Čech cocycle has an actual lower-degree
cochain primitive. -/
theorem coverCechCochains_exists_primitive (M : ModuleCat.{0} R) (U : ι → Set α)
    (hU : ∀ x, ∃ i, x ∈ U i) (k : ℕ)
    (c : Representatives.cochainCocycles (coverCechCochains M U) (k + 1)) :
    ∃ b : (coverCechCochains M U).X k,
      ((coverCechCochains M U).d k (k + 1)) b = c.1 := by
  let := ModuleCat.subsingleton_of_isZero
    (coverCechCochains_exactAt_succ M U hU k).isZero_homology
  have h : Representatives.cochainClass (coverCechCochains M U) (k + 1) c =
      Representatives.cochainClass (coverCechCochains M U) (k + 1) 0 := Subsingleton.elim _ _
  simpa using (Representatives.cochainClass_eq_iff_exists_succ (coverCechCochains M U) k c 0).mp h

/-- Families of coefficient-valued functions which agree at every point
belonging to two of the covering subsets. -/
def coverMatchingFunctions (M : ModuleCat.{0} R) (U : ι → Set α) :
    Submodule R ((i : ι) → U i → M) where
  carrier c := ∀ (i j : ι) (x : α) (hi : x ∈ U i) (hj : x ∈ U j),
    c i ⟨x, hi⟩ = c j ⟨x, hj⟩
  zero_mem' := fun _ _ _ _ _ => rfl
  add_mem' := by
    intro c d hc hd i j x hi hj
    change c i ⟨x, hi⟩ + d i ⟨x, hi⟩ = c j ⟨x, hj⟩ + d j ⟨x, hj⟩
    rw [hc i j x hi hj, hd i j x hi hj]
  smul_mem' := by
    intro a c hc i j x hi hj
    change a • c i ⟨x, hi⟩ = a • c j ⟨x, hj⟩
    rw [hc i j x hi hj]

/-- Restriction and gluing give a linear equivalence between global
functions and compatible families on a genuine set cover. -/
def coverFunctionGluingEquiv (M : ModuleCat.{0} R) (U : ι → Set α)
    (hU : ∀ x, ∃ i, x ∈ U i) :
    (α → M) ≃ₗ[R] coverMatchingFunctions M U where
  toFun c := ⟨fun _ x => c x, fun _ _ _ _ _ => rfl⟩
  invFun c x := c.1 (Classical.choose (hU x)) ⟨x, Classical.choose_spec (hU x)⟩
  left_inv c := rfl
  right_inv c := by
    apply Subtype.ext
    funext i x
    exact c.2 (Classical.choose (hU x)) i x (Classical.choose_spec (hU x)) x.2
  map_add' c d := rfl
  map_smul' a c := rfl

@[simp]
theorem coverFunctionGluingEquiv_apply (M : ModuleCat.{0} R) (U : ι → Set α)
    (hU : ∀ x, ∃ i, x ∈ U i) (c : α → M) (i : ι) (x : U i) :
    (coverFunctionGluingEquiv M U hU c).1 i x = c x := rfl

/-- The glued function restricts to the given function on every cover
member, independently of the member chosen in its definition. -/
@[simp]
theorem coverFunctionGluingEquiv_symm_apply (M : ModuleCat.{0} R) (U : ι → Set α)
    (hU : ∀ x, ∃ i, x ∈ U i) (c : coverMatchingFunctions M U) (i : ι) (x : U i) :
    (coverFunctionGluingEquiv M U hU).symm c x = c.1 i x :=
  c.2 (Classical.choose (hU x)) i x (Classical.choose_spec (hU x)) x.2

variable (X : TopCat.{0}) (U : ι → Set X)

/-- The actual Čech cochain row in fixed singular degree `n`, resolving
cochains on simplices lying in at least one spatial family member. -/
abbrev smallSingularCechCochains (M : ModuleCat.{0} R) (n : ℕ) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  coverCechCochains M (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X U n)

/-- Cochains in Čech degree `k` are all coefficient-valued functions on
the genuine Čech `k`-simplices of the small-simplex cover. -/
def smallSingularCechDegreewiseFunctionIso (M : ModuleCat.{0} R) (n k : ℕ) :
    (smallSingularCechCochains X U M n).X k ≅
      ModuleCat.of R ((DeRham.Comparison.CechCoverRows.coverCechNerve
        (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X U n)).left _⦋k⦌ → M) :=
  Coefficients.degreewiseFunctionIso _ M k

/-- The Čech row differential is the usual alternating sum of face
restrictions, in the proved function coordinates. -/
theorem smallSingularCechCochains_d_apply (M : ModuleCat.{0} R) (n k : ℕ)
    (c : (smallSingularCechCochains X U M n).X k)
    (σ : (DeRham.Comparison.CechCoverRows.coverCechNerve
      (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X U n)).left _⦋k + 1⦌) :
    (smallSingularCechDegreewiseFunctionIso X U M n (k + 1)).hom
        ((smallSingularCechCochains X U M n).d k (k + 1) c) σ =
      ∑ j : Fin (k + 2), ((-1 : ℤ) ^ j.val) •
        (smallSingularCechDegreewiseFunctionIso X U M n k).hom c
          ((DeRham.Comparison.CechCoverRows.coverCechNerve
            (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X U n)).left.δ j σ) :=
  Formulas.degreewiseFunctionIso_coboundary _ M c σ

/-- The positive Čech degrees of every small-singular row are exact. -/
theorem smallSingularCechCochains_exactAt_succ (M : ModuleCat.{0} R) (n k : ℕ) :
    (smallSingularCechCochains X U M n).ExactAt (k + 1) :=
  coverCechCochains_exactAt_succ M (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X U n)
    (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover_covers X U n) k

/-- The zeroth cohomology of the small-singular Čech row is the existing
degree-`n` small singular cochain object. -/
def smallSingularCechCochainsHomologyZeroIso (M : ModuleCat.{0} R) (n : ℕ) :
    (smallSingularCechCochains X U M n).homology 0 ≅
      (DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X U).X n :=
  coverCechCochainsHomologyZeroIso M (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X U n)
    (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover_covers X U n) ≪≫
    (DeRham.Comparison.SmallSingularCochains.smallSingularDegreewiseFunctionIso M X U n).symm

/-- Positive Čech cocycles of small singular cochains have actual
primitives in the preceding Čech degree. -/
theorem smallSingularCechCochains_exists_primitive (M : ModuleCat.{0} R) (n k : ℕ)
    (c : Representatives.cochainCocycles (smallSingularCechCochains X U M n) (k + 1)) :
    ∃ b : (smallSingularCechCochains X U M n).X k,
      ((smallSingularCechCochains X U M n).d k (k + 1)) b = c.1 :=
  coverCechCochains_exists_primitive M (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X U n)
    (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover_covers X U n) k c

/-- Compatible local values on singular simplices are exactly actual
small singular cochains, through the previously proved function coordinates. -/
def smallSingularCochainGluingEquiv (M : ModuleCat.{0} R) (n : ℕ) :
    (DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X U).X n ≃ₗ[R]
      coverMatchingFunctions M (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X U n) :=
  (DeRham.Comparison.SmallSingularCochains.smallSingularDegreewiseFunctionIso M X U n).toLinearEquiv.trans
    (coverFunctionGluingEquiv M (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X U n)
      (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover_covers X U n))

@[simp]
theorem smallSingularCochainGluingEquiv_apply (M : ModuleCat.{0} R) (n : ℕ)
    (c : (DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X U).X n) (i : ι)
    (σ : DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X U n i) :
    (smallSingularCochainGluingEquiv X U M n c).1 i σ =
      (DeRham.Comparison.SmallSingularCochains.smallSingularDegreewiseFunctionIso M X U n).hom c σ.1 := rfl

/-- Singular simplices of a subspace are exactly ambient singular
simplices whose images lie in that subset. -/
def singularSimplexSubtypeEquiv (s : Set X) (n : ℕ) :
    Basic.singularSimplices (TopCat.of s) n ≃
      {σ : Basic.singularSimplices X n //
        Set.range (X.toSSetObjEquiv (op ⦋n⦌) σ) ⊆ s} where
  toFun σ :=
    ⟨(X.toSSetObjEquiv (op ⦋n⦌)).symm
      ⟨fun t => (((TopCat.of s).toSSetObjEquiv (op ⦋n⦌) σ) t).1,
        continuous_subtype_val.comp
          ((TopCat.of s).toSSetObjEquiv (op ⦋n⦌) σ).continuous⟩,
      by
        rintro _ ⟨t, rfl⟩
        exact (((TopCat.of s).toSSetObjEquiv (op ⦋n⦌) σ) t).2⟩
  invFun σ :=
    ((TopCat.of s).toSSetObjEquiv (op ⦋n⦌)).symm
      ⟨fun t => ⟨(X.toSSetObjEquiv (op ⦋n⦌) σ.1) t, σ.2 ⟨t, rfl⟩⟩,
        ((X.toSSetObjEquiv (op ⦋n⦌) σ.1).continuous).subtype_mk _⟩
  left_inv σ := by
    apply ((TopCat.of s).toSSetObjEquiv (op ⦋n⦌)).injective
    ext t
    rfl
  right_inv σ := by
    apply Subtype.ext
    apply (X.toSSetObjEquiv (op ⦋n⦌)).injective
    ext t
    rfl

/-- Each member of the small-simplex cover is exactly the set of
singular simplices in the corresponding spatial subspace. -/
def localSmallSingularSimplexEquiv (n : ℕ) (i : ι) :
    Basic.singularSimplices (TopCat.of (U i)) n ≃
      DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X U n i :=
  (singularSimplexSubtypeEquiv X (U i) n).trans
    { toFun := fun σ => ⟨⟨σ.1, ⟨i, σ.2⟩⟩, σ.2⟩
      invFun := fun σ => ⟨σ.1.1, σ.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- A simplex in a spatial cover member includes canonically into the
small singular simplicial subset. -/
def localSmallSingularMap (i : ι) :
    TopCat.toSSet.obj (TopCat.of (U i)) ⟶
      (DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet) where
  app n := TypeCat.ofHom (fun σ => (localSmallSingularSimplexEquiv X U n.unop.len i σ).1)
  naturality n m f := by
    apply ConcreteCategory.ext_apply
    intro σ
    apply Subtype.ext
    apply (X.toSSetObjEquiv m).injective
    ext t
    rfl

/-- Actual restriction of small singular cochains to one cover member. -/
def smallSingularLocalRestriction (M : ModuleCat.{0} R) (i : ι) :
    DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X U ⟶ Basic.singularCochains M (TopCat.of (U i)) :=
  Functor.simplicialPullback M (localSmallSingularMap X U i)

/-- The local function factors in the gluing theorem are the actual
singular cochain modules of the spatial cover members. -/
def localSingularCochainFunctionsEquiv (M : ModuleCat.{0} R) (n : ℕ) :
    ((i : ι) → (Basic.singularCochains M (TopCat.of (U i))).X n) ≃ₗ[R]
      ((i : ι) → DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X U n i → M) :=
  LinearEquiv.piCongrRight (fun i =>
    (Coefficients.singularDegreewiseFunctionIso M (TopCat.of (U i)) n).toLinearEquiv.trans
      (LinearEquiv.piCongrLeft' R
        (fun _ : Basic.singularSimplices (TopCat.of (U i)) n => M)
        (localSmallSingularSimplexEquiv X U n i)))

/-- Families of actual local singular cochains whose simplex values
agree whenever the ambient singular simplex is the same. -/
def matchingLocalSingularCochains (M : ModuleCat.{0} R) (n : ℕ) :
    Submodule R ((i : ι) → (Basic.singularCochains M (TopCat.of (U i))).X n) :=
  (coverMatchingFunctions M (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X U n)).comap
    (localSingularCochainFunctionsEquiv X U M n).toLinearMap

/-- Matching means equality of the two local values whenever the same
ambient singular simplex lies in both spatial subsets. -/
theorem mem_matchingLocalSingularCochains_iff (M : ModuleCat.{0} R) (n : ℕ)
    (c : (i : ι) → (Basic.singularCochains M (TopCat.of (U i))).X n) :
    c ∈ matchingLocalSingularCochains X U M n ↔
      ∀ (i j : ι) (σ : DeRham.Comparison.CechCoverRows.SmallSingularSimplex X U n)
        (hi : σ ∈ DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X U n i)
        (hj : σ ∈ DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X U n j),
        (Coefficients.singularDegreewiseFunctionIso M (TopCat.of (U i)) n).hom (c i)
            ((localSmallSingularSimplexEquiv X U n i).symm ⟨σ, hi⟩) =
          (Coefficients.singularDegreewiseFunctionIso M (TopCat.of (U j)) n).hom (c j)
            ((localSmallSingularSimplexEquiv X U n j).symm ⟨σ, hj⟩) := Iff.rfl

/-- Actual local singular cochains glue uniquely to an actual
cover-small singular cochain. -/
def smallSingularCochainLocalGluingEquiv (M : ModuleCat.{0} R) (n : ℕ) :
    (DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X U).X n ≃ₗ[R]
      matchingLocalSingularCochains X U M n :=
  (smallSingularCochainGluingEquiv X U M n).trans
    ((localSingularCochainFunctionsEquiv X U M n).ofSubmodule'
      (coverMatchingFunctions M (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X U n))).symm

/-- The restrictions have exactly the function coordinates used in
constructing the gluing equivalence. -/
theorem localSingularRestriction_functionCoordinates (M : ModuleCat.{0} R) (n : ℕ)
    (c : (DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X U).X n) :
    localSingularCochainFunctionsEquiv X U M n
        (fun i => (smallSingularLocalRestriction X U M i).f n c) =
      (smallSingularCochainGluingEquiv X U M n c).1 := by
  funext i σ
  change (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj (TopCat.of (U i))) M n).hom
      ((Functor.simplicialPullback M (localSmallSingularMap X U i)).f n c)
        ((localSmallSingularSimplexEquiv X U n i).symm σ) = _
  rw [Formulas.degreewiseFunctionIso_pullback]
  change (DeRham.Comparison.SmallSingularCochains.smallSingularDegreewiseFunctionIso M X U n).hom c
      ((localSmallSingularSimplexEquiv X U n i)
        ((localSmallSingularSimplexEquiv X U n i).symm σ)).1 =
    (DeRham.Comparison.SmallSingularCochains.smallSingularDegreewiseFunctionIso M X U n).hom c σ.1
  rw [Equiv.apply_symm_apply]

/-- The gluing equivalence restricts a small cochain by the genuine
singular pullback to each spatial cover member. -/
theorem smallSingularCochainLocalGluingEquiv_apply (M : ModuleCat.{0} R) (n : ℕ)
    (c : (DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X U).X n) (i : ι) :
    (smallSingularCochainLocalGluingEquiv X U M n c).1 i =
      (smallSingularLocalRestriction X U M i).f n c := by
  have h : localSingularCochainFunctionsEquiv X U M n
      (smallSingularCochainLocalGluingEquiv X U M n c).1 =
        (smallSingularCochainGluingEquiv X U M n c).1 := by
    change localSingularCochainFunctionsEquiv X U M n
        (((localSingularCochainFunctionsEquiv X U M n).ofSubmodule'
          (coverMatchingFunctions M (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X U n))).symm
            (smallSingularCochainGluingEquiv X U M n c)).1 = _
    rw [LinearEquiv.ofSubmodule'_symm_apply, LinearEquiv.apply_symm_apply]
  exact congrFun ((localSingularCochainFunctionsEquiv X U M n).injective
    (h.trans (localSingularRestriction_functionCoordinates X U M n c).symm)) i

/-- Every compatible family of actual local singular cochains has one
and only one cover-small cochain with those genuine restrictions. -/
theorem existsUnique_smallSingularCochain_gluing (M : ModuleCat.{0} R) (n : ℕ)
    (c : matchingLocalSingularCochains X U M n) :
    ∃! b : (DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X U).X n,
      ∀ i, (smallSingularLocalRestriction X U M i).f n b = c.1 i := by
  refine ⟨(smallSingularCochainLocalGluingEquiv X U M n).symm c, ?_, ?_⟩
  · intro i
    rw [← smallSingularCochainLocalGluingEquiv_apply, LinearEquiv.apply_symm_apply]
  · intro b hb
    apply (smallSingularCochainLocalGluingEquiv X U M n).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    funext i
    rw [smallSingularCochainLocalGluingEquiv_apply, hb i]

end

end OAI.AlgebraicTopology.Cohomology.Singular.SmallCochainCech
