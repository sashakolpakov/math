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
import OAI.AlgebraicTopology.Singular.SubdivisionBarycentricAllDegrees
import Mathlib.Logic.Equiv.PartialEquiv

/-! # Subdivision Barycentric Outer Faces -/

namespace OAI.AlgebraicTopology.Singular.SubdivisionBarycentricOuterFaces

noncomputable section

/-!

# The outer-face identity for barycentric fundamental chains

This file reindexes the surviving outer faces of the signed maximal-flag sum by the omitted
vertex and the induced ordering of its complement. It completes the boundary calculation and
therefore supplies the unconditional natural barycentric subdivision chain morphism.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits PartialOrder Simplicial

/-- `Finset.image` does not depend propositionally on the chosen decidable equality. -/
theorem finsetImage_decidableEq_independent
    {α β : Type*} (d₁ d₂ : DecidableEq β) (f : α → β) (s : Finset α) :
    @Finset.image α β d₁ f s = @Finset.image α β d₂ f s := by
  ext y
  simp only [Finset.mem_image]

/-- Insert the omitted vertex `p` at the final position of an ordering of its complement. -/
noncomputable def insertOmittedVertexLast {n : ℕ}
    (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin (n + 2)) where
  toFun := Fin.lastCases p (fun k ↦ p.succAbove (τ k))
  invFun := Fin.succAboveCases p (Fin.last (n + 1))
    (fun k ↦ (τ.symm k).castSucc)
  left_inv i := by refine Fin.lastCases ?_ (fun k ↦ ?_) i <;> simp
  right_inv i := by refine Fin.succAboveCases p ?_ (fun k ↦ ?_) i <;> simp

@[simp]
theorem insertOmittedVertexLast_apply_last {n : ℕ}
    (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    insertOmittedVertexLast p τ (Fin.last (n + 1)) = p := by
  simp [insertOmittedVertexLast]

@[simp]
theorem insertOmittedVertexLast_apply_castSucc {n : ℕ}
    (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    insertOmittedVertexLast p τ k.castSucc = p.succAbove (τ k) := by
  simp [insertOmittedVertexLast]

/-- Every permutation is uniquely an omitted final vertex together with an ordering of its
complement. -/
noncomputable def insertOmittedVertexLastEquiv (n : ℕ) :
    Fin (n + 2) × Equiv.Perm (Fin (n + 1)) ≃
      Equiv.Perm (Fin (n + 2)) :=
  Equiv.ofBijective (fun pτ ↦ insertOmittedVertexLast pτ.1 pτ.2) <| by
    rw [Fintype.bijective_iff_injective_and_card]
    constructor
    · rintro ⟨p, τ⟩ ⟨q, υ⟩ h
      have hp := congrArg (fun σ ↦ σ (Fin.last (n + 1))) h
      simp only [insertOmittedVertexLast_apply_last] at hp
      subst q
      congr 1
      refine Equiv.ext fun k ↦ p.succAbove_right_injective ?_
      have hk := congrArg (fun σ ↦ σ k.castSucc) h
      simpa only [insertOmittedVertexLast_apply_castSucc] using hk
    · simp [Fintype.card_prod, Fintype.card_perm, Nat.factorial_succ]

@[simp]
theorem insertOmittedVertexLastEquiv_apply
    (n : ℕ) (pτ : Fin (n + 2) × Equiv.Perm (Fin (n + 1))) :
    insertOmittedVertexLastEquiv n pτ =
      insertOmittedVertexLast pτ.1 pτ.2 :=
  rfl

/-- The reindexing equivalence records the omitted final vertex in its first coordinate. -/
@[simp]
theorem insertOmittedVertexLastEquiv_symm_fst
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 2))) :
    ((insertOmittedVertexLastEquiv n).symm σ).1 = σ (Fin.last (n + 1)) := by
  let pτ := (insertOmittedVertexLastEquiv n).symm σ
  have h := (insertOmittedVertexLastEquiv n).apply_symm_apply σ
  change insertOmittedVertexLast pτ.1 pτ.2 = σ at h
  have hlast := congrArg (fun e ↦ e (Fin.last (n + 1))) h
  simpa only [insertOmittedVertexLast_apply_last] using hlast

/-- `Fin.castSucc` identifies `Fin (n+1)` with all vertices except the last one. -/
def finCastSuccEquivNotLast (n : ℕ) :
    Fin (n + 1) ≃ {i : Fin (n + 2) // i ≠ Fin.last (n + 1)} where
  toFun i := ⟨i.castSucc, Fin.castSucc_lt_last i |>.ne⟩
  invFun i := i.1.castPred i.2
  left_inv _ := Fin.castPred_castSucc
  right_inv i := Subtype.ext (Fin.castSucc_castPred i.1 i.2)

/-- Inserting the last vertex last extends a permutation while fixing that vertex. -/
theorem insertOmittedVertexLast_last_eq_extendDomain
    {n : ℕ} (τ : Equiv.Perm (Fin (n + 1))) :
    insertOmittedVertexLast (Fin.last (n + 1)) τ =
      τ.extendDomain (finCastSuccEquivNotLast n) := by
  apply Equiv.ext
  intro i
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · rw [insertOmittedVertexLast_apply_last]
    symm
    apply Equiv.Perm.extendDomain_apply_not_subtype
    simp
  · rw [insertOmittedVertexLast_apply_castSucc]
    change (Fin.last (n + 1)).succAbove (τ k) =
      τ.extendDomain (finCastSuccEquivNotLast n) ↑((finCastSuccEquivNotLast n) k)
    rw [Equiv.Perm.extendDomain_apply_image τ (finCastSuccEquivNotLast n) k]
    simp [finCastSuccEquivNotLast]

/-- Inserting `p` last factors into the order-preserving cycle from the last vertex to `p`,
followed by extension of the complement ordering. -/
theorem insertOmittedVertexLast_eq_cycle_mul_extend {n : ℕ}
    (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    insertOmittedVertexLast p τ =
      p.cycleIcc (Fin.last (n + 1)) *
        τ.extendDomain (finCastSuccEquivNotLast n) := by
  rw [← insertOmittedVertexLast_last_eq_extendDomain]
  apply Equiv.ext
  intro i
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · rw [insertOmittedVertexLast_apply_last, Equiv.Perm.mul_apply,
      insertOmittedVertexLast_apply_last]
    exact (Fin.cycleIcc_of_last (Fin.le_last p)).symm
  · rw [insertOmittedVertexLast_apply_castSucc, Equiv.Perm.mul_apply,
      insertOmittedVertexLast_apply_castSucc]
    exact (congrFun
      (Fin.cycleIcc_comp_succAbove p (Fin.last (n + 1)) (Fin.le_last p)) (τ k)).symm

/-- The sign of an ordering with omitted vertex `p` inserted last. -/
theorem permutationSignInteger_insertOmittedVertexLast {n : ℕ}
    (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    SubdivisionBarycentricAllDegrees.permutationSignInteger (insertOmittedVertexLast p τ) =
      (-1 : ℤ) ^ (n + 1 - p.val) * SubdivisionBarycentricAllDegrees.permutationSignInteger τ := by
  rw [insertOmittedVertexLast_eq_cycle_mul_extend]
  simp only [SubdivisionBarycentricAllDegrees.permutationSignInteger, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_extendDomain, Fin.sign_cycleIcc_of_le (Fin.le_last p),
    Fin.val_last]
  simp

/-- Multiplying by the boundary sign of the final face leaves exactly the usual sign of the
omitted vertex. -/
theorem outerFaceCoefficient_insertOmittedVertexLast {n : ℕ}
    (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    SubdivisionBarycentricAllDegrees.permutationSignInteger (insertOmittedVertexLast p τ) * (-1 : ℤ) ^ (n + 1) =
      (-1 : ℤ) ^ p.val * SubdivisionBarycentricAllDegrees.permutationSignInteger τ := by
  rw [permutationSignInteger_insertOmittedVertexLast]
  have hp : p.val ≤ n + 1 := Nat.le_of_lt_succ p.isLt
  have hadd : n + 1 - p.val + p.val = n + 1 := Nat.sub_add_cancel hp
  nth_rewrite 2 [← hadd]
  rw [pow_add]
  calc
    (-1 : ℤ) ^ (n + 1 - p.val) * SubdivisionBarycentricAllDegrees.permutationSignInteger τ *
          ((-1 : ℤ) ^ (n + 1 - p.val) * (-1 : ℤ) ^ p.val) =
        (((-1 : ℤ) ^ (n + 1 - p.val)) *
          ((-1 : ℤ) ^ (n + 1 - p.val))) *
            ((-1 : ℤ) ^ p.val * SubdivisionBarycentricAllDegrees.permutationSignInteger τ) := by ring
    _ = ((-1 : ℤ) * (-1 : ℤ)) ^ (n + 1 - p.val) *
          ((-1 : ℤ) ^ p.val * SubdivisionBarycentricAllDegrees.permutationSignInteger τ) := by rw [mul_pow]
    _ = _ := by norm_num

/-- Deleting the final (full-set) prefix of an inserted ordering is the subdivided face obtained
by omitting `p`. -/
theorem permutationMaximalFlagSimplex_outerFace_insert {n : ℕ}
    (p : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    (SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).δ (Fin.last (n + 1))
        (SubdivisionBarycentricAllDegrees.permutationMaximalFlagSimplex (insertOmittedVertexLast p τ)) =
      (SimplexCategory.sd.{0}.map (SimplexCategory.δ p)).app
        (Opposite.op (SimplexCategory.mk n))
        (SubdivisionBarycentricAllDegrees.permutationMaximalFlagSimplex τ) := by
  refine ComposableArrows.ext (fun k ↦ ?_) (fun k hk ↦ ?_)
  · change SubdivisionBarycentricAllDegrees.permutationPrefixChain (insertOmittedVertexLast p τ)
      ((Fin.last (n + 1)).succAbove k) =
        (SubdivisionBarycentricAllDegrees.permutationPrefixChain τ k).map
          (SimplexCategory.toPartOrd.{0}.map (SimplexCategory.δ p)).hom
    apply NonemptyFiniteChains.ext
    have hfinset :
        SubdivisionBarycentricAllDegrees.permutationPrefixFinset (insertOmittedVertexLast p τ)
            ((Fin.last (n + 1)).succAbove k) =
          Finset.image (fun i : ULift.{0} (Fin (n + 1)) ↦
            ULift.up (p.succAbove i.down)) (SubdivisionBarycentricAllDegrees.permutationPrefixFinset τ k) := by
      rw [Fin.succAbove_last]
      unfold SubdivisionBarycentricAllDegrees.permutationPrefixFinset
      rw [← Fin.finsetImage_castSucc_Iic k, Finset.image_image, Finset.image_image]
      apply Finset.image_congr
      intro a ha
      simp
    unfold SubdivisionBarycentricAllDegrees.permutationPrefixChain SubdivisionBarycentricChains.nonemptyFiniteChainOfFinset NonemptyFiniteChains.map
    dsimp only
    have hmap (i : ULift.{0} (Fin (n + 1))) :
        (SimplexCategory.toPartOrd.{0}.map (SimplexCategory.δ p)).hom i =
          ULift.up (p.succAbove i.down) := by
      induction i
      rfl
    calc
      _ = Finset.image (fun i : ULift.{0} (Fin (n + 1)) ↦
          ULift.up (p.succAbove i.down)) (SubdivisionBarycentricAllDegrees.permutationPrefixFinset τ k) := hfinset
      _ = _ := by
        rw [show (fun i : ULift.{0} (Fin (n + 1)) ↦
          ULift.up (p.succAbove i.down)) =
            (SimplexCategory.toPartOrd.{0}.map (SimplexCategory.δ p)).hom from
              funext (fun i ↦ (hmap i).symm)]
        apply finsetImage_decidableEq_independent
  · apply Subsingleton.elim

/-- The surviving outer faces reindex to the alternating sum of subdivided simplex faces. -/
theorem barycentricOuterFaceIdentity (n : ℕ) :
    SubdivisionBarycentricAllDegrees.subdividedSimplexOuterFaceSum n = SubdivisionBarycentricAllDegrees.subdividedSimplexAlternatingFaceChain n := by
  rw [SubdivisionBarycentricAllDegrees.subdividedSimplexOuterFaceSum, SubdivisionBarycentricAllDegrees.subdividedSimplexAlternatingFaceChain,
    ← Equiv.sum_comp (insertOmittedVertexLastEquiv n), Fintype.sum_prod_type]
  simp only [insertOmittedVertexLastEquiv_apply, smul_smul, Fin.val_last,
    outerFaceCoefficient_insertOmittedVertexLast,
    permutationMaximalFlagSimplex_outerFace_insert]
  simp_rw [SubdivisionBarycentricAllDegrees.subdividedSimplexFundamentalChain, Preadditive.sum_comp,
    Preadditive.zsmul_comp, Finset.smul_sum, SSet.ι_chainComplexMap_f]
  simp only [smul_smul]

/-- The signed maximal-flag fundamental chains satisfy the complete alternating boundary
identity in every degree: all interior faces cancel, and the surviving outer faces reindex by
the previous theorem. -/
theorem barycentricFundamentalBoundaryIdentity (n : ℕ) :
    SubdivisionBarycentricAllDegrees.subdividedSimplexFundamentalChain (n + 1) ≫
        ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n =
      SubdivisionBarycentricAllDegrees.subdividedSimplexAlternatingFaceChain n := by
  rw [SubdivisionBarycentricAllDegrees.subdividedSimplexFundamentalChain_boundary_eq_outer n]
  exact barycentricOuterFaceIdentity n

/-- The boundary identity transports to the left-Kan-extension standard simplices. -/
theorem subdividedStandardSimplexFundamentalChain_boundary (n : ℕ) :
    SubdivisionBarycentricAllDegrees.subdividedStandardSimplexFundamentalChain (n + 1) ≫
        ((SSet.sd.obj (Δ[n + 1] : SSet.{0})).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n =
      SubdivisionBarycentricAllDegrees.subdividedStandardSimplexAlternatingFaceChain n := by
  let F := SSet.chainComplexMap
    (SSet.stdSimplex.sdIso.inv.app (SimplexCategory.mk (n + 1)))
    (AddCommGrpCat.of ℤ)
  change (SubdivisionBarycentricAllDegrees.subdividedSimplexFundamentalChain (n + 1) ≫ F.f (n + 1)) ≫ _ = _
  have hcomm := F.comm (n + 1) n
  have hpre := congrArg
    (fun k ↦ SubdivisionBarycentricAllDegrees.subdividedSimplexFundamentalChain (n + 1) ≫ k) hcomm
  calc
    _ = SubdivisionBarycentricAllDegrees.subdividedSimplexFundamentalChain (n + 1) ≫
        (F.f (n + 1) ≫ _) := Category.assoc _ _ _
    _ = SubdivisionBarycentricAllDegrees.subdividedSimplexFundamentalChain (n + 1) ≫
        (_ ≫ F.f n) := hpre
    _ = (SubdivisionBarycentricAllDegrees.subdividedSimplexFundamentalChain (n + 1) ≫
        ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk (n + 1))).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n) ≫ F.f n := (Category.assoc _ _ _).symm
    _ = SubdivisionBarycentricAllDegrees.subdividedSimplexAlternatingFaceChain n ≫ F.f n := by
      rw [barycentricFundamentalBoundaryIdentity n]
    _ = _ := by
      rw [SubdivisionBarycentricAllDegrees.subdividedSimplexAlternatingFaceChain, Preadditive.sum_comp]
      simp only [Preadditive.zsmul_comp, Category.assoc]
      rw [SubdivisionBarycentricAllDegrees.subdividedStandardSimplexAlternatingFaceChain]
      apply Finset.sum_congr rfl
      intro i hi
      rw [SubdivisionBarycentricAllDegrees.subdividedStandardSimplexFundamentalChain, Category.assoc,
        SubdivisionBarycentricAllDegrees.subdividedStandardSimplexFace_naturality]

/-- The subdivided chain of an arbitrary simplex has the expected alternating boundary. -/
theorem barycentricSubdivisionSimplexChain_boundary
    (X : SSet.{0}) (n : ℕ)
    (x : X.obj (Opposite.op (SimplexCategory.mk (n + 1)))) :
    SubdivisionBarycentricAllDegrees.barycentricSubdivisionSimplexChain X (n + 1) x ≫
        ((SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n =
      SubdivisionBarycentricAllDegrees.barycentricSubdivisionAlternatingFaceChain X n x := by
  let F := SSet.chainComplexMap (SSet.sd.map (SSet.yonedaEquiv.symm x))
    (AddCommGrpCat.of ℤ)
  change (SubdivisionBarycentricAllDegrees.subdividedStandardSimplexFundamentalChain (n + 1) ≫ F.f (n + 1)) ≫
    _ = _
  have hcomm := F.comm (n + 1) n
  have hpre := congrArg
    (fun k ↦ SubdivisionBarycentricAllDegrees.subdividedStandardSimplexFundamentalChain (n + 1) ≫ k) hcomm
  calc
    _ = SubdivisionBarycentricAllDegrees.subdividedStandardSimplexFundamentalChain (n + 1) ≫
        (F.f (n + 1) ≫ _) := Category.assoc _ _ _
    _ = SubdivisionBarycentricAllDegrees.subdividedStandardSimplexFundamentalChain (n + 1) ≫
        (_ ≫ F.f n) := hpre
    _ = (SubdivisionBarycentricAllDegrees.subdividedStandardSimplexFundamentalChain (n + 1) ≫
        ((SSet.sd.obj (Δ[n + 1] : SSet.{0})).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n) ≫ F.f n := (Category.assoc _ _ _).symm
    _ = SubdivisionBarycentricAllDegrees.subdividedStandardSimplexAlternatingFaceChain n ≫ F.f n := by
      rw [subdividedStandardSimplexFundamentalChain_boundary n]
    _ = _ := by
      rw [SubdivisionBarycentricAllDegrees.subdividedStandardSimplexAlternatingFaceChain, Preadditive.sum_comp]
      simp only [Preadditive.zsmul_comp, Category.assoc]
      rw [SubdivisionBarycentricAllDegrees.barycentricSubdivisionAlternatingFaceChain]
      apply Finset.sum_congr rfl
      intro i hi
      rw [SubdivisionBarycentricAllDegrees.barycentricSubdivisionSimplexChain]
      apply congrArg (fun k ↦ ((-1 : ℤ) ^ i.val) • k)
      rw [SubdivisionBarycentricAllDegrees.subdividedFace_then_simplex_naturality]

/-- The degreewise barycentric subdivision components commute with the differentials. -/
theorem barycentricSubdivisionComponent_comp_d (X : SSet.{0}) (n : ℕ) :
    SubdivisionBarycentricAllDegrees.barycentricSubdivisionComponent X (n + 1) ≫
        ((SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n =
      (X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n ≫
        SubdivisionBarycentricAllDegrees.barycentricSubdivisionComponent X n := by
  apply X.chainComplex_hom_ext
  intro x
  rw [← Category.assoc, SubdivisionBarycentricAllDegrees.iota_barycentricSubdivisionComponent,
    barycentricSubdivisionSimplexChain_boundary]
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, SubdivisionBarycentricAllDegrees.iota_barycentricSubdivisionComponent]
  rfl

/-- The unconditional natural barycentric subdivision chain morphism. -/
noncomputable def barycentricSubdivisionChainMapCanonical (X : SSet.{0}) :
    X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      (SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ) :=
  ChainComplex.ofHom (SubdivisionBarycentricAllDegrees.barycentricSubdivisionComponent X)
    (barycentricSubdivisionComponent_comp_d X)

@[simp]
theorem barycentricSubdivisionChainMapCanonical_f
    (X : SSet.{0}) (n : ℕ) :
    (barycentricSubdivisionChainMapCanonical X).f n =
      SubdivisionBarycentricAllDegrees.barycentricSubdivisionComponent X n :=
  rfl

end

end OAI.AlgebraicTopology.Singular.SubdivisionBarycentricOuterFaces
