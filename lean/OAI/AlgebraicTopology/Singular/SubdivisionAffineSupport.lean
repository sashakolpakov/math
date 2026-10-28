/-
Copyright 2026 Paul Lezeau and The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
This file has been modified.
-/
import OAI.AlgebraicTopology.Singular.SubdivisionAffineMesh
import OAI.AlgebraicTopology.Singular.SubdivisionAffineRelativeMesh

/-! # Subdivision Affine Support -/

namespace OAI.AlgebraicTopology.Singular.SubdivisionAffineSupport

noncomputable section

/-!

# Support of iterated affine subdivision

This file connects the permutation expansion of affine barycentric subdivision with the
geometric ancestry cells used in the mesh estimate. It then lifts an iterate whose ancestry
cells are subordinate to a cover into the cover-small singular chain complex.
-/

open _root_.AlgebraicTopology _root_.CategoryTheory _root_.CategoryTheory.Limits Set Simplicial

/-- The singular simplex obtained by restricting `x` to one iterated affine ancestry cell. -/
noncomputable def iteratedAffineCellSingularSimplex
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (ancestry : List (SubdivisionAffineMesh.TopAffineFlag n)) :
    (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)) :=
  (X.toSSetObjEquiv _).symm
    ((X.toSSetObjEquiv _ x).comp (SubdivisionAffineMesh.iteratedAffineCellMap n ancestry))

@[simp]
theorem toSSetObjEquiv_iteratedAffineCellSingularSimplex_apply
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (ancestry : List (SubdivisionAffineMesh.TopAffineFlag n))
    (w : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    X.toSSetObjEquiv _
        (iteratedAffineCellSingularSimplex X n x ancestry) w =
      X.toSSetObjEquiv _ x (SubdivisionAffineMesh.iteratedAffineCellMap n ancestry w) := by
  rfl

@[simp]
theorem iteratedAffineCellSingularSimplex_nil
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    iteratedAffineCellSingularSimplex X n x [] = x := by
  apply (X.toSSetObjEquiv _).injective
  rfl

/-- Adding the newest flag to an ancestry is the same as restricting the parent cell by that
affine flag. -/
theorem iteratedAffineCellSingularSimplex_cons
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (F : SubdivisionAffineMesh.TopAffineFlag n) (ancestry : List (SubdivisionAffineMesh.TopAffineFlag n)) :
    iteratedAffineCellSingularSimplex X n x (F :: ancestry) =
      (TopCat.toSSet.map
        (SubdivisionAffine.singularSimplexTopCatMap X n
          (iteratedAffineCellSingularSimplex X n x ancestry))).app _
        (SubdivisionAffine.affineFlagSingularSimplex n n F) := by
  apply (X.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro w
  rfl

/-- Restricting a parent ancestry cell by one more flag adds that flag at the head of the
ancestry. -/
theorem iteratedAffineCellSingularSimplex_singleton_parent
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (F : SubdivisionAffineMesh.TopAffineFlag n) (ancestry : List (SubdivisionAffineMesh.TopAffineFlag n)) :
    iteratedAffineCellSingularSimplex X n
        (iteratedAffineCellSingularSimplex X n x ancestry) [F] =
      iteratedAffineCellSingularSimplex X n x (F :: ancestry) := by
  calc
    iteratedAffineCellSingularSimplex X n
        (iteratedAffineCellSingularSimplex X n x ancestry) [F] =
        (TopCat.toSSet.map
          (SubdivisionAffine.singularSimplexTopCatMap X n
            (iteratedAffineCellSingularSimplex X n x ancestry))).app _
          (SubdivisionAffine.affineFlagSingularSimplex n n F) := by
            rw [iteratedAffineCellSingularSimplex_cons,
              iteratedAffineCellSingularSimplex_nil]
    _ = iteratedAffineCellSingularSimplex X n x (F :: ancestry) :=
      (iteratedAffineCellSingularSimplex_cons X n x F ancestry).symm

/-- One affine subdivision of a generator is exactly the signed sum over permutation maximal
flags. -/
theorem affineSubdivisionSingularSimplexChain_eq_permutation_sum
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    SubdivisionAffine.affineSubdivisionSingularSimplexChain X n x =
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        SubdivisionBarycentricAllDegrees.permutationSignInteger σ •
          (TopCat.toSSet.obj X).ιChainComplex
            (iteratedAffineCellSingularSimplex X n x
              [SubdivisionBarycentricAllDegrees.permutationMaximalFlagSimplex σ]) := by
  rw [SubdivisionAffine.affineSubdivisionSingularSimplexChain,
    SubdivisionAffine.affineSubdividedSimplexFundamentalChain,
    SubdivisionBarycentricAllDegrees.subdividedSimplexFundamentalChain, Preadditive.sum_comp,
    Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Preadditive.zsmul_comp,
    SubdivisionAffine.affineFlagChainMap_f, SubdivisionAffine.iota_affineFlagChainComponent,
    SSet.ι_chainComplexMap_f]
  apply congrArg (fun f ↦ SubdivisionBarycentricAllDegrees.permutationSignInteger σ • f)
  rw [iteratedAffineCellSingularSimplex_cons,
    iteratedAffineCellSingularSimplex_nil]

/-- A depth-`m` choice of one permutation maximal flag at every subdivision stage. -/
abbrev AffinePermutationAncestry (n m : ℕ) :=
  Fin m → Equiv.Perm (Fin (n + 1))

/-- The list of affine flags encoded by a permutation ancestry, newest first. -/
noncomputable def affinePermutationAncestryFlags
    (n m : ℕ) (a : AffinePermutationAncestry n m) :
    List (SubdivisionAffineMesh.TopAffineFlag n) :=
  List.ofFn fun i ↦ SubdivisionBarycentricAllDegrees.permutationMaximalFlagSimplex (a i)

/-- The product of the orientation signs along a permutation ancestry. -/
noncomputable def affinePermutationAncestrySign
    (n m : ℕ) (a : AffinePermutationAncestry n m) : ℤ :=
  ∏ i, SubdivisionBarycentricAllDegrees.permutationSignInteger (a i)

@[simp]
theorem affinePermutationAncestryFlags_zero
    (n : ℕ) (a : AffinePermutationAncestry n 0) :
    affinePermutationAncestryFlags n 0 a = [] := by
  simp [affinePermutationAncestryFlags]

@[simp]
theorem affinePermutationAncestrySign_zero
    (n : ℕ) (a : AffinePermutationAncestry n 0) :
    affinePermutationAncestrySign n 0 a = 1 := by
  simp [affinePermutationAncestrySign]

@[simp]
theorem affinePermutationAncestryFlags_cons
    (n m : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (a : AffinePermutationAncestry n m) :
    affinePermutationAncestryFlags n (m + 1) (Fin.cons σ a) =
      SubdivisionBarycentricAllDegrees.permutationMaximalFlagSimplex σ ::
        affinePermutationAncestryFlags n m a := by
  simp [affinePermutationAncestryFlags]

@[simp]
theorem affinePermutationAncestrySign_cons
    (n m : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (a : AffinePermutationAncestry n m) :
    affinePermutationAncestrySign n (m + 1) (Fin.cons σ a) =
      SubdivisionBarycentricAllDegrees.permutationSignInteger σ * affinePermutationAncestrySign n m a := by
  simp [affinePermutationAncestrySign, Fin.prod_univ_succ]

/-- The exact generator expansion after `m` affine subdivisions. Its summands are precisely the
singular simplices obtained from depth-`m` affine ancestries. -/
theorem iota_affineSingularSubdivisionIterate_eq_ancestry_sum
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    ∀ m : ℕ,
      (TopCat.toSSet.obj X).ιChainComplex x ≫
          (SubdivisionAffineIteration.affineSingularSubdivisionIterate X m).f n =
        ∑ a : AffinePermutationAncestry n m,
          affinePermutationAncestrySign n m a •
            (TopCat.toSSet.obj X).ιChainComplex
              (iteratedAffineCellSingularSimplex X n x
                (affinePermutationAncestryFlags n m a)) := by
  intro m
  induction m with
  | zero =>
      classical
      simp only [SubdivisionAffineIteration.affineSingularSubdivisionIterate_zero]
      rw [Fintype.sum_unique]
      simp
  | succ m ih =>
      classical
      rw [SubdivisionAffineIteration.affineSingularSubdivisionIterate_succ]
      change ((TopCat.toSSet.obj X).ιChainComplex x ≫
          (SubdivisionAffineIteration.affineSingularSubdivisionIterate X m).f n) ≫
            (SubdivisionAffine.affineSingularSubdivisionChainMap X).f n = _
      rw [ih, Preadditive.sum_comp]
      simp only [Preadditive.zsmul_comp,
        SubdivisionAffine.affineSingularSubdivisionChainMap_f,
        SubdivisionAffine.iota_affineSingularSubdivisionComponent,
        affineSubdivisionSingularSimplexChain_eq_permutation_sum,
        Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm, ← Fintype.sum_prod_type']
      apply Fintype.sum_equiv
        (Fin.consEquiv (fun _ : Fin (m + 1) ↦
          Equiv.Perm (Fin (n + 1)))) _ _
      rintro ⟨σ, a⟩
      change (affinePermutationAncestrySign n m a *
          SubdivisionBarycentricAllDegrees.permutationSignInteger σ) • _ =
        affinePermutationAncestrySign n (m + 1) (Fin.cons σ a) •
          (TopCat.toSSet.obj X).ιChainComplex
            (iteratedAffineCellSingularSimplex X n x
              (affinePermutationAncestryFlags n (m + 1) (Fin.cons σ a)))
      rw [affinePermutationAncestrySign_cons,
        affinePermutationAncestryFlags_cons, mul_comm,
        iteratedAffineCellSingularSimplex_singleton_parent]

variable {ι : Type} (X : TopCat.{0}) (U : ι → Set X)

/-- A geometric ancestry cell subordinate to one cover member defines a cover-small singular
simplex. -/
theorem iteratedAffineCellSingularSimplex_mem_coverSmall
    (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (ancestry : List (SubdivisionAffineMesh.TopAffineFlag n))
    (hsmall : ∃ i, X.toSSetObjEquiv _ x ''
      Set.range (SubdivisionAffineMesh.iteratedAffineCellMap n ancestry) ⊆ U i) :
    iteratedAffineCellSingularSimplex X n x ancestry ∈
      (ExcisionCoverSmall.coverSmallSingularSubcomplex X U).obj
        (Opposite.op (SimplexCategory.mk n)) := by
  rw [ExcisionCoverSmall.mem_coverSmallSingularSubcomplex_iff_exists_preimage]
  obtain ⟨i, hi⟩ := hsmall
  let f : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U i) :=
    ⟨fun w ↦
      ⟨X.toSSetObjEquiv _ x (SubdivisionAffineMesh.iteratedAffineCellMap n ancestry w),
        hi ⟨SubdivisionAffineMesh.iteratedAffineCellMap n ancestry w, ⟨w, rfl⟩, rfl⟩⟩,
      Continuous.subtype_mk
        ((X.toSSetObjEquiv _ x).continuous.comp
          (SubdivisionAffineMesh.iteratedAffineCellMap n ancestry).continuous) _⟩
  refine ⟨i, (TopCat.toSSetObjEquiv _ _).symm f, ?_⟩
  apply (X.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro w
  rfl

/-- The cover-small simplex corresponding to a subordinate ancestry cell. -/
noncomputable def coverSmallIteratedAffineCellSimplex
    (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (ancestry : List (SubdivisionAffineMesh.TopAffineFlag n))
    (hsmall : ∃ i, X.toSSetObjEquiv _ x ''
      Set.range (SubdivisionAffineMesh.iteratedAffineCellMap n ancestry) ⊆ U i) :
    (ExcisionCoverSmall.coverSmallSingularSubcomplex X U : SSet).obj
      (Opposite.op (SimplexCategory.mk n)) :=
  ⟨iteratedAffineCellSingularSimplex X n x ancestry,
    iteratedAffineCellSingularSimplex_mem_coverSmall X U n x ancestry hsmall⟩

@[simp]
theorem coverSmallIteratedAffineCellSimplex_val
    (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (ancestry : List (SubdivisionAffineMesh.TopAffineFlag n))
    (hsmall : ∃ i, X.toSSetObjEquiv _ x ''
      Set.range (SubdivisionAffineMesh.iteratedAffineCellMap n ancestry) ⊆ U i) :
    (coverSmallIteratedAffineCellSimplex X U n x ancestry hsmall).1 =
      iteratedAffineCellSingularSimplex X n x ancestry :=
  rfl

/-- The signed ancestry expansion, lifted generator by generator to cover-small chains. -/
noncomputable def coverSmallAffineAncestryLiftChain
    (n m : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (hsmall : ∀ a : AffinePermutationAncestry n m,
      ∃ i, X.toSSetObjEquiv _ x ''
        Set.range (SubdivisionAffineMesh.iteratedAffineCellMap n
          (affinePermutationAncestryFlags n m a)) ⊆ U i) :
    AddCommGrpCat.of ℤ ⟶
      (ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).X n :=
  ∑ a : AffinePermutationAncestry n m,
    affinePermutationAncestrySign n m a •
      (ExcisionCoverSmall.coverSmallSingularSubcomplex X U : SSet).ιChainComplex
        (coverSmallIteratedAffineCellSimplex X U n x
          (affinePermutationAncestryFlags n m a) (hsmall a))

/-- The lifted ancestry chain maps to the affine-subdivision iterate of its original
generator. -/
theorem coverSmallAffineAncestryLiftChain_comp_inclusion
    (n m : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (hsmall : ∀ a : AffinePermutationAncestry n m,
      ∃ i, X.toSSetObjEquiv _ x ''
        Set.range (SubdivisionAffineMesh.iteratedAffineCellMap n
          (affinePermutationAncestryFlags n m a)) ⊆ U i) :
    coverSmallAffineAncestryLiftChain X U n m x hsmall ≫
        (ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U).f n =
      (TopCat.toSSet.obj X).ιChainComplex x ≫
        (SubdivisionAffineIteration.affineSingularSubdivisionIterate X m).f n := by
  change coverSmallAffineAncestryLiftChain X U n m x hsmall ≫
      (SSet.chainComplexMap (ExcisionCoverSmall.coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)).f n = _
  rw [coverSmallAffineAncestryLiftChain, Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp, SSet.ι_chainComplexMap_f]
  exact (iota_affineSingularSubdivisionIterate_eq_ancestry_sum X n x m).symm

/-- If every depth-`m` ancestry cell of a generator is subordinate to the cover, its subdivided
chain lies in the degreewise range of the cover-small inclusion. -/
theorem affineSingularSubdivisionIterate_generator_mem_range_of_ancestries
    (n m : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (hsmall : ∀ a : AffinePermutationAncestry n m,
      ∃ i, X.toSSetObjEquiv _ x ''
        Set.range (SubdivisionAffineMesh.iteratedAffineCellMap n
          (affinePermutationAncestryFlags n m a)) ⊆ U i) :
    (SubdivisionAffineIteration.affineSingularSubdivisionIterate X m).f n
        ((TopCat.toSSet.obj X).ιChainComplex
          (R := AddCommGrpCat.of ℤ) x 1) ∈
      Set.range ((ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U).f n) := by
  refine ⟨coverSmallAffineAncestryLiftChain X U n m x hsmall 1, ?_⟩
  exact ConcreteCategory.congr_hom
    (coverSmallAffineAncestryLiftChain_comp_inclusion X U n m x hsmall) 1

@[simp]
theorem length_affinePermutationAncestryFlags
    (n m : ℕ) (a : AffinePermutationAncestry n m) :
    (affinePermutationAncestryFlags n m a).length = m := by
  simp [affinePermutationAncestryFlags]

/-- Once an iterate lies in the range of the cover-small inclusion, every later iterate does as
well. -/
theorem affineSingularSubdivisionIterate_mem_range_add
    (n m r : ℕ)
    (c : (ExcisionCoverSmall.IntegralSingularChainComplexObj X).X n)
    (h : (SubdivisionAffineIteration.affineSingularSubdivisionIterate X m).f n c ∈
      Set.range ((ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U).f n)) :
    (SubdivisionAffineIteration.affineSingularSubdivisionIterate X (m + r)).f n c ∈
      Set.range ((ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U).f n) := by
  obtain ⟨y, hy⟩ := h
  refine ⟨(SubdivisionAffineIteration.coverSmallAffineSubdivisionIterate X U r).f n y, ?_⟩
  have hcomm := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.f n)
      (SubdivisionAffineIteration.coverSmallAffineSubdivisionIterate_comp_inclusion X U r)) y
  have hmiddle :
      (SubdivisionAffineIteration.affineSingularSubdivisionIterate X r).f n
          ((ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U).f n y) =
        (SubdivisionAffineIteration.affineSingularSubdivisionIterate X r).f n
          ((SubdivisionAffineIteration.affineSingularSubdivisionIterate X m).f n c) :=
    congrArg ((SubdivisionAffineIteration.affineSingularSubdivisionIterate X r).f n) hy
  have htotal :
      (SubdivisionAffineIteration.affineSingularSubdivisionIterate X r).f n
          ((SubdivisionAffineIteration.affineSingularSubdivisionIterate X m).f n c) =
        (SubdivisionAffineIteration.affineSingularSubdivisionIterate X (m + r)).f n c := by
    rw [SubdivisionAffineMesh.affineSingularSubdivisionIterate_add]
    rfl
  exact hcomm.trans (hmiddle.trans htotal)

/-- Chains which become cover-small after some (chain-dependent) number of affine subdivisions
form an additive subgroup. -/
noncomputable def affineSubdivisionEventuallySmallAddSubgroup
    (n : ℕ) : AddSubgroup ((ExcisionCoverSmall.IntegralSingularChainComplexObj X).X n) where
  carrier := {c | ∃ m : ℕ,
    (SubdivisionAffineIteration.affineSingularSubdivisionIterate X m).f n c ∈
      Set.range ((ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U).f n)}
  zero_mem' :=
    ⟨0, 0, ((ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U).f n).hom.map_zero.trans
      ((SubdivisionAffineIteration.affineSingularSubdivisionIterate X 0).f n).hom.map_zero.symm⟩
  add_mem' := by
    rintro c d ⟨m, hm⟩ ⟨r, hr⟩
    have hm' := affineSingularSubdivisionIterate_mem_range_add
      X U n m r c hm
    have hr' := affineSingularSubdivisionIterate_mem_range_add
      X U n r m d hr
    rw [Nat.add_comm r m] at hr'
    obtain ⟨yc, hyc⟩ := hm'
    obtain ⟨yd, hyd⟩ := hr'
    refine ⟨m + r, yc + yd, ?_⟩
    simp only [map_add]
    rw [hyc, hyd]
    exact ((SubdivisionAffineIteration.affineSingularSubdivisionIterate X (m + r)).f n).hom.map_add c d |>.symm
  neg_mem' := by
    rintro c ⟨m, hm⟩
    obtain ⟨y, hy⟩ := hm
    refine ⟨m, -y, ?_⟩
    simp only [map_neg]
    rw [hy]
    exact ((SubdivisionAffineIteration.affineSingularSubdivisionIterate X m).f n).hom.map_neg c |>.symm

/-- Generatorwise subordinate permutation ancestries suffice for every chain: the required
subdivision depth may depend on the chain. -/
theorem exists_affineSubdivisionIterate_mem_range_of_generator_ancestries
    (n : ℕ)
    (hsmall : ∀ x : (TopCat.toSSet.obj X).obj
        (Opposite.op (SimplexCategory.mk n)),
      ∃ m : ℕ, ∀ a : AffinePermutationAncestry n m,
        ∃ i, X.toSSetObjEquiv _ x ''
          Set.range (SubdivisionAffineMesh.iteratedAffineCellMap n
            (affinePermutationAncestryFlags n m a)) ⊆ U i) :
    ∀ c : (ExcisionCoverSmall.IntegralSingularChainComplexObj X).X n,
      ∃ m : ℕ, (SubdivisionAffineIteration.affineSingularSubdivisionIterate X m).f n c ∈
        Set.range ((ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U).f n) := by
  let P := affineSubdivisionEventuallySmallAddSubgroup X U n
  let Q := AddCommGrpCat.of ((ExcisionCoverSmall.IntegralSingularChainComplexObj X).X n ⧸ P)
  let q : (ExcisionCoverSmall.IntegralSingularChainComplexObj X).X n ⟶ Q :=
    AddCommGrpCat.ofHom (QuotientAddGroup.mk' P)
  have hq : q = 0 := by
    apply (TopCat.toSSet.obj X).chainComplex_hom_ext
    intro x
    let j : AddCommGrpCat.of ℤ ⟶ (ExcisionCoverSmall.IntegralSingularChainComplexObj X).X n :=
      (TopCat.toSSet.obj X).ιChainComplex x
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    change QuotientAddGroup.mk' P (j z) = 0
    obtain ⟨m, hm⟩ := hsmall x
    have hgen : j 1 ∈ P :=
      ⟨m, affineSingularSubdivisionIterate_generator_mem_range_of_ancestries
        X U n m x hm⟩
    have hzsmul := P.zsmul_mem hgen z
    have heq : j z = z • j 1 := by
      calc
        j z = j (z • (1 : ℤ)) := by simp
        _ = z • j 1 := j.hom.map_zsmul z 1
    rw [← heq] at hzsmul
    show j z ∈ (QuotientAddGroup.mk' P).ker
    rwa [QuotientAddGroup.ker_mk']
  intro c
  have hc : QuotientAddGroup.mk' P c = 0 := ConcreteCategory.congr_hom hq c
  change c ∈ P
  have hcker : c ∈ (QuotientAddGroup.mk' P).ker := hc
  rwa [QuotientAddGroup.ker_mk'] at hcker

/-- If all ancestry cells of one common depth are subordinate for each singular simplex, then
every chain in that degree has a cover-small subdivision iterate. -/
theorem exists_affineSubdivisionIterate_mem_range_of_ancestries
    (n : ℕ)
    (hsmall : ∀ x : (TopCat.toSSet.obj X).obj
        (Opposite.op (SimplexCategory.mk n)),
      ∃ m : ℕ, ∀ ancestry : List (SubdivisionAffineMesh.TopAffineFlag n),
        ancestry.length = m →
          ∃ i, X.toSSetObjEquiv _ x ''
            Set.range (SubdivisionAffineMesh.iteratedAffineCellMap n ancestry) ⊆ U i) :
    ∀ c : (ExcisionCoverSmall.IntegralSingularChainComplexObj X).X n,
      ∃ m : ℕ, (SubdivisionAffineIteration.affineSingularSubdivisionIterate X m).f n c ∈
        Set.range ((ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U).f n) := by
  apply exists_affineSubdivisionIterate_mem_range_of_generator_ancestries X U n
  intro x
  obtain ⟨m, hm⟩ := hsmall x
  exact ⟨m, fun a ↦ hm (affinePermutationAncestryFlags n m a)
    (length_affinePermutationAncestryFlags n m a)⟩

/-- Cover-subordination of every depth-`m` ancestry cell (with a depth depending on the original
simplex and degree) implies affine eventual smallness for all singular chains. -/
theorem coverSmallAffineSubdivisionEventuallySmall_of_ancestries
    (hsmall : ∀ (n : ℕ) (x : (TopCat.toSSet.obj X).obj
        (Opposite.op (SimplexCategory.mk n))),
      ∃ m : ℕ, ∀ ancestry : List (SubdivisionAffineMesh.TopAffineFlag n),
        ancestry.length = m →
          ∃ i, X.toSSetObjEquiv _ x ''
            Set.range (SubdivisionAffineMesh.iteratedAffineCellMap n ancestry) ⊆ U i) :
    ∀ (n : ℕ) (x : (ExcisionCoverSmall.IntegralSingularChainComplexObj X).X n),
      ∃ (m : ℕ) (y : (ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).X n),
        (ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U).f n y =
          (SubdivisionAffineIteration.affineSingularSubdivisionIterate X m).f n x := by
  apply SubdivisionAffineMesh.coverSmallAffineSubdivisionEventuallySmall_of_iterate_mem_range X U
  intro n c
  exact exists_affineSubdivisionIterate_mem_range_of_ancestries
    X U n (hsmall n) c

/-- Zero-dimensional singular simplices are already subordinate to any covering family. -/
theorem exists_zero_dimensional_ancestry_depth_subordinate
    (hUcover : ⋃ i, U i = Set.univ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk 0))) :
    ∃ m : ℕ, ∀ ancestry : List (SubdivisionAffineMesh.TopAffineFlag 0),
      ancestry.length = m →
        ∃ i, X.toSSetObjEquiv _ x ''
          Set.range (SubdivisionAffineMesh.iteratedAffineCellMap 0 ancestry) ⊆ U i := by
  refine ⟨0, fun ancestry hlength ↦ ?_⟩
  cases ancestry with
  | cons F ancestry => simp at hlength
  | nil =>
  let w₀ : Convexity.StdSimplex ℝ (Fin (0 + 1)) := Classical.arbitrary _
  have hwcover : X.toSSetObjEquiv _ x w₀ ∈ ⋃ i, U i := by
    rw [hUcover]
    trivial
  simp only [Set.mem_iUnion] at hwcover
  obtain ⟨i, hi⟩ := hwcover
  refine ⟨i, ?_⟩
  rintro y ⟨z, ⟨w, rfl⟩, rfl⟩
  have hw : w = w₀ := by
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 1)).injective
    funext j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    have h1 : w.weights 0 = 1 :=
      (Fin.sum_univ_one w.weights).symm.trans w.total_of_fintype
    have h2 : w₀.weights 0 = 1 :=
      (Fin.sum_univ_one w₀.weights).symm.trans w₀.total_of_fintype
    exact h1.trans h2.symm
  simpa [hw] using hi

/-- Every finite singular chain becomes subordinate to an open cover after enough affine
barycentric subdivisions: the relative mesh contraction handles the positive degrees, and
degree zero is already small. -/
theorem coverSmallAffineSubdivisionEventuallySmall_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    ∀ (n : ℕ) (x : (ExcisionCoverSmall.IntegralSingularChainComplexObj X).X n),
      ∃ (m : ℕ) (y : (ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).X n),
        (ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U).f n y =
          (SubdivisionAffineIteration.affineSingularSubdivisionIterate X m).f n x := by
  apply coverSmallAffineSubdivisionEventuallySmall_of_ancestries X U
  intro n x
  cases n with
  | zero =>
      exact exists_zero_dimensional_ancestry_depth_subordinate X U hUcover x
  | succ n =>
      exact SubdivisionAffineRelativeMesh.exists_iteratedAffineCell_depth_subordinate X U hUopen hUcover
        (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) x

end

end OAI.AlgebraicTopology.Singular.SubdivisionAffineSupport
