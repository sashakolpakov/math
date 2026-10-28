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
import OAI.AlgebraicTopology.Singular.SubdivisionBarycentricHomotopy

/-! # Standard Simplex Cone -/

namespace OAI.AlgebraicTopology.Singular.StandardSimplexCone

noncomputable section

/-!

# The cone contraction on standard-simplex chains

Prepending the zero vertex defines an extra degeneracy on every standard simplex. On integral
simplicial chains this is the classical cone operator. This file constructs it on the
coproduct basis used by `SSet.chainComplex` and proves its positive-degree contraction identity.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits PartialOrder Simplicial

/-- Prepend the zero vertex to a simplex of `Δ[m]`. -/
noncomputable def standardSimplexZeroConeSimplex
    (m n : ℕ)
    (x : (Δ[m] : SSet.{0}).obj (Opposite.op (SimplexCategory.mk n))) :
    (Δ[m] : SSet.{0}).obj (Opposite.op (SimplexCategory.mk (n + 1))) :=
  SSet.stdSimplex.objEquiv.symm
    (SSet.Augmented.StandardSimplex.shift (SSet.stdSimplex.objEquiv x))

/-- Removing the newly prepended zero vertex recovers the original simplex. -/
@[simp]
theorem standardSimplexZeroConeSimplex_delta_zero
    (m n : ℕ)
    (x : (Δ[m] : SSet.{0}).obj (Opposite.op (SimplexCategory.mk n))) :
    (Δ[m] : SSet.{0}).δ 0 (standardSimplexZeroConeSimplex m n x) = x :=
  ConcreteCategory.congr_hom
    ((SSet.Augmented.StandardSimplex.extraDegeneracy (SimplexCategory.mk m)).s_comp_δ₀ n) x

/-- Every later face of a cone is the cone on the preceding face. -/
@[simp]
theorem standardSimplexZeroConeSimplex_delta_succ
    (m n : ℕ) (i : Fin (n + 2))
    (x : (Δ[m] : SSet.{0}).obj (Opposite.op (SimplexCategory.mk (n + 1)))) :
    (Δ[m] : SSet.{0}).δ i.succ (standardSimplexZeroConeSimplex m (n + 1) x) =
      standardSimplexZeroConeSimplex m n ((Δ[m] : SSet.{0}).δ i x) :=
  ConcreteCategory.congr_hom
    ((SSet.Augmented.StandardSimplex.extraDegeneracy (SimplexCategory.mk m)).s_comp_δ n i) x

/-- The integral cone operator on all basis simplices in degree `n`. -/
noncomputable def standardSimplexZeroConeComponent
    (m n : ℕ) :
    ((Δ[m] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      ((Δ[m] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ)).X (n + 1) :=
  Sigma.desc (fun x ↦
    (Δ[m] : SSet.{0}).ιChainComplex
      (standardSimplexZeroConeSimplex m n x))

@[reassoc (attr := simp)]
theorem iota_standardSimplexZeroConeComponent
    (m n : ℕ)
    (x : (Δ[m] : SSet.{0}).obj (Opposite.op (SimplexCategory.mk n))) :
    (Δ[m] : SSet.{0}).ιChainComplex x ≫
        standardSimplexZeroConeComponent m n =
      (Δ[m] : SSet.{0}).ιChainComplex
        (standardSimplexZeroConeSimplex m n x) :=
  Sigma.ι_comp_desc _ _

/-- In every positive degree, the zero-vertex cone contracts the integral chains of a standard
simplex. -/
theorem standardSimplexZeroConeComponent_boundary_succ
    (m n : ℕ) :
    standardSimplexZeroConeComponent m (n + 1) ≫
          ((Δ[m] : SSet.{0}).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) +
        ((Δ[m] : SSet.{0}).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 1) n ≫
          standardSimplexZeroConeComponent m n =
      𝟙 (((Δ[m] : SSet.{0}).chainComplex
        (AddCommGrpCat.of ℤ)).X (n + 1)) := by
  apply (Δ[m] : SSet.{0}).chainComplex_hom_ext
  intro x
  simp only [Preadditive.comp_add, Category.comp_id]
  rw [← Category.assoc, iota_standardSimplexZeroConeComponent, SSet.ιChainComplex_d,
    ← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, iota_standardSimplexZeroConeComponent]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul,
    standardSimplexZeroConeSimplex_delta_zero,
    standardSimplexZeroConeSimplex_delta_succ, Fin.val_succ, pow_succ]
  rw [add_assoc, ← Finset.sum_add_distrib]
  simp

/-- The positive-degree cone fills every cycle in a standard simplex. -/
theorem standardSimplexZeroConeComponent_fills_cycle
    (m n : ℕ)
    (z : AddCommGrpCat.of ℤ ⟶
      ((Δ[m] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ)).X (n + 1))
    (hz : z ≫
      ((Δ[m] : SSet.{0}).chainComplex
        (AddCommGrpCat.of ℤ)).d (n + 1) n = 0) :
    z ≫ standardSimplexZeroConeComponent m (n + 1) ≫
        ((Δ[m] : SSet.{0}).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) = z := by
  have h := congrArg (fun f ↦ z ≫ f)
    (standardSimplexZeroConeComponent_boundary_succ m n)
  simp only [Preadditive.comp_add, Category.comp_id] at h
  simp only [← Category.assoc, hz, zero_comp, add_zero] at h
  exact h

/-- Subdivision followed by last vertex, minus the identity, as a chain map. -/
noncomputable def barycentricLastVertexDiscrepancyChainMap (X : SSet.{0}) :
    X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      X.chainComplex (AddCommGrpCat.of ℤ) :=
  SubdivisionBarycentricOuterFaces.barycentricSubdivisionChainMapCanonical X ≫
      SubdivisionBasic.subdivisionLastVertexChainMap X - 𝟙 _

/-- The universal discrepancy is the value of the discrepancy chain map on the universal
top-dimensional simplex. -/
theorem standardBarycentricLastVertexDiscrepancy_eq_top_comp
    (n : ℕ) :
    SubdivisionBarycentricHomotopy.standardBarycentricLastVertexDiscrepancy n =
      (Δ[n] : SSet.{0}).ιChainComplex (SubdivisionBarycentricHomotopy.standardSimplexTopSimplex n) ≫
        (barycentricLastVertexDiscrepancyChainMap
          (Δ[n] : SSet.{0})).f n := by
  rw [SubdivisionBarycentricHomotopy.standardBarycentricLastVertexDiscrepancy,
    barycentricLastVertexDiscrepancyChainMap]
  simp only [HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply,
    HomologicalComplex.id_f, Preadditive.comp_sub, Category.comp_id]
  rw [← Category.assoc, SubdivisionBarycentricOuterFaces.barycentricSubdivisionChainMapCanonical_f,
    SubdivisionBarycentricAllDegrees.iota_barycentricSubdivisionComponent]

/-- Evaluating the discrepancy chain map on a simplex is transport of the universal
discrepancy along that simplex. -/
theorem iota_barycentricLastVertexDiscrepancyChainMap
    (X : SSet.{0}) (n : ℕ)
    (x : X.obj (Opposite.op (SimplexCategory.mk n))) :
    X.ιChainComplex x ≫
        (barycentricLastVertexDiscrepancyChainMap X).f n =
      SubdivisionBarycentricHomotopy.standardBarycentricLastVertexDiscrepancy n ≫
        (SSet.chainComplexMap (SSet.yonedaEquiv.symm x)
          (AddCommGrpCat.of ℤ)).f n := by
  rw [SubdivisionBarycentricHomotopy.standardBarycentricLastVertexDiscrepancy_transport,
    barycentricLastVertexDiscrepancyChainMap]
  simp only [HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply,
    HomologicalComplex.id_f, Preadditive.comp_sub, Category.comp_id]
  rw [← Category.assoc, SubdivisionBarycentricOuterFaces.barycentricSubdivisionChainMapCanonical_f,
    SubdivisionBarycentricAllDegrees.iota_barycentricSubdivisionComponent]

/-- A face of the universal simplex represents the corresponding standard coface map. -/
theorem yonedaEquiv_symm_standardSimplexTopSimplex_delta
    (n : ℕ) (i : Fin (n + 2)) :
    SSet.yonedaEquiv.symm
        ((Δ[n + 1] : SSet.{0}).δ i
          (SubdivisionBarycentricHomotopy.standardSimplexTopSimplex (n + 1))) =
      SSet.stdSimplex.map (SimplexCategory.δ i) := by
  have h := SSet.stdSimplex.δ_comp_yonedaEquiv_symm
    (SubdivisionBarycentricHomotopy.standardSimplexTopSimplex (n + 1)) i
  rw [SubdivisionBarycentricHomotopy.standardSimplexTopSimplex,
    SSet.yonedaEquiv_symm_stdSimplex_id, Category.comp_id] at h
  exact h.symm

/-- The boundary of the universal discrepancy is the alternating transport of the
lower-dimensional universal discrepancy over all faces. -/
theorem standardBarycentricLastVertexDiscrepancy_boundary
    (n : ℕ) :
    SubdivisionBarycentricHomotopy.standardBarycentricLastVertexDiscrepancy (n + 1) ≫
        ((Δ[n + 1] : SSet.{0}).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (SubdivisionBarycentricHomotopy.standardBarycentricLastVertexDiscrepancy n ≫
          (SSet.chainComplexMap
            (SSet.yonedaEquiv.symm
              ((Δ[n + 1] : SSet.{0}).δ i
                (SubdivisionBarycentricHomotopy.standardSimplexTopSimplex (n + 1))))
            (AddCommGrpCat.of ℤ)).f n) := by
  rw [standardBarycentricLastVertexDiscrepancy_eq_top_comp, Category.assoc,
    (barycentricLastVertexDiscrepancyChainMap (Δ[n + 1] : SSet.{0})).comm,
    ← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← iota_barycentricLastVertexDiscrepancyChainMap]

/-- The same discrepancy boundary formula, written using the standard coface maps appearing in
the recursive prism equation. -/
theorem standardBarycentricLastVertexDiscrepancy_boundary_stdSimplex
    (n : ℕ) :
    SubdivisionBarycentricHomotopy.standardBarycentricLastVertexDiscrepancy (n + 1) ≫
        ((Δ[n + 1] : SSet.{0}).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (SubdivisionBarycentricHomotopy.standardBarycentricLastVertexDiscrepancy n ≫
          (SSet.chainComplexMap
            (SSet.stdSimplex.map (SimplexCategory.δ i))
            (AddCommGrpCat.of ℤ)).f n) := by
  rw [standardBarycentricLastVertexDiscrepancy_boundary]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [yonedaEquiv_symm_standardSimplexTopSimplex_delta]

/-- The unique maximal flag of the zero-simplex is its singleton vertex. -/
theorem permutationMaximalFlagSimplex_one_zero :
    SubdivisionBarycentricAllDegrees.permutationMaximalFlagSimplex (1 : Equiv.Perm (Fin 1)) =
      SubdivisionBarycentricChains.subdividedZeroSimplexVertex := by
  refine ComposableArrows.ext (fun k ↦ ?_) (fun k hk ↦ ?_)
  · fin_cases k
    apply NonemptyFiniteChains.ext
    change SubdivisionBarycentricAllDegrees.permutationPrefixFinset (1 : Equiv.Perm (Fin 1)) 0 =
      {ULift.up (0 : Fin 1)}
    ext z
    rcases z with ⟨z⟩
    fin_cases z
    simp [SubdivisionBarycentricAllDegrees.permutationPrefixFinset]
  · apply Subsingleton.elim

/-- The canonical all-degree subdivision chain map agrees in degree zero with the direct
vertex-level construction. -/
theorem barycentricSubdivisionChainMapCanonical_f_zero
    (X : SSet.{0}) :
    (SubdivisionBarycentricOuterFaces.barycentricSubdivisionChainMapCanonical X).f 0 =
      SubdivisionBarycentricChains.barycentricSubdivisionChainMapZero X := by
  apply X.chainComplex_hom_ext
  intro x
  rw [SubdivisionBarycentricOuterFaces.barycentricSubdivisionChainMapCanonical_f,
    SubdivisionBarycentricAllDegrees.iota_barycentricSubdivisionComponent,
    SubdivisionBarycentricChains.iota_barycentricSubdivisionChainMapZero]
  simp [SubdivisionBarycentricAllDegrees.barycentricSubdivisionSimplexChain,
    SubdivisionBarycentricAllDegrees.subdividedStandardSimplexFundamentalChain,
    SubdivisionBarycentricAllDegrees.subdividedSimplexFundamentalChain,
    SubdivisionBarycentricChains.barycentricSubdivisionVertex, SubdivisionBarycentricAllDegrees.permutationSignInteger,
    permutationMaximalFlagSimplex_one_zero, SubdivisionBarycentricChains.subdividedStandardZeroVertex]

/-- The universal discrepancy vanishes in degree zero. -/
@[simp]
theorem standardBarycentricLastVertexDiscrepancy_zero :
    SubdivisionBarycentricHomotopy.standardBarycentricLastVertexDiscrepancy 0 = 0 := by
  rw [standardBarycentricLastVertexDiscrepancy_eq_top_comp,
    barycentricLastVertexDiscrepancyChainMap]
  simp only [HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply,
    HomologicalComplex.id_f]
  rw [barycentricSubdivisionChainMapCanonical_f_zero,
    SubdivisionBarycentricChains.barycentricSubdivisionChainMapZero_comp_lastVertex]
  simp

/-- Transport one universal degree-raising chain along every simplex of an arbitrary simplicial
set. -/
noncomputable def universalStandardSimplexPrismComponent
    (n : ℕ)
    (p : AddCommGrpCat.of ℤ ⟶
      ((Δ[n] : SSet.{0}).chainComplex
        (AddCommGrpCat.of ℤ)).X (n + 1))
    (X : SSet.{0}) :
    (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (X.chainComplex (AddCommGrpCat.of ℤ)).X (n + 1) :=
  Sigma.desc (fun x ↦ p ≫
    (SSet.chainComplexMap (SSet.yonedaEquiv.symm x)
      (AddCommGrpCat.of ℤ)).f (n + 1))

@[reassoc (attr := simp)]
theorem iota_universalStandardSimplexPrismComponent
    (n : ℕ)
    (p : AddCommGrpCat.of ℤ ⟶
      ((Δ[n] : SSet.{0}).chainComplex
        (AddCommGrpCat.of ℤ)).X (n + 1))
    (X : SSet.{0})
    (x : X.obj (Opposite.op (SimplexCategory.mk n))) :
    X.ιChainComplex x ≫ universalStandardSimplexPrismComponent n p X =
      p ≫ (SSet.chainComplexMap (SSet.yonedaEquiv.symm x)
        (AddCommGrpCat.of ℤ)).f (n + 1) := by
  apply Sigma.ι_comp_desc

/-- The face-prism sum is the boundary of the universal top simplex followed by the transported
lower-dimensional prism operator. -/
theorem standardPrismFaceChain_eq_top_boundary_comp
    (prism : ∀ n : ℕ, AddCommGrpCat.of ℤ ⟶
      ((Δ[n] : SSet.{0}).chainComplex
        (AddCommGrpCat.of ℤ)).X (n + 1))
    (n : ℕ) :
    SubdivisionBarycentricHomotopy.standardPrismFaceChain prism (n + 1) =
      (Δ[n + 1] : SSet.{0}).ιChainComplex
          (SubdivisionBarycentricHomotopy.standardSimplexTopSimplex (n + 1)) ≫
        ((Δ[n + 1] : SSet.{0}).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n ≫
        universalStandardSimplexPrismComponent n (prism n)
          (Δ[n + 1] : SSet.{0}) := by
  rw [SubdivisionBarycentricHomotopy.standardPrismFaceChain, ← Category.assoc,
    SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp,
    iota_universalStandardSimplexPrismComponent]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [yonedaEquiv_symm_standardSimplexTopSimplex_delta]

/-- Transporting a raw face-prism sum is the source boundary followed by the transported raw
prism operator. -/
theorem standardPrismFaceChain_transport_raw
    (prism : ∀ n : ℕ, AddCommGrpCat.of ℤ ⟶
      ((Δ[n] : SSet.{0}).chainComplex
        (AddCommGrpCat.of ℤ)).X (n + 1))
    (X : SSet.{0}) (n : ℕ)
    (x : X.obj (Opposite.op (SimplexCategory.mk (n + 1)))) :
    SubdivisionBarycentricHomotopy.standardPrismFaceChain prism (n + 1) ≫
        (SSet.chainComplexMap (SSet.yonedaEquiv.symm x)
          (AddCommGrpCat.of ℤ)).f (n + 1) =
      X.ιChainComplex x ≫
        (X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n ≫
        universalStandardSimplexPrismComponent n (prism n) X := by
  rw [SubdivisionBarycentricHomotopy.standardPrismFaceChain, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, Category.assoc]
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp,
    iota_universalStandardSimplexPrismComponent]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  apply congrArg (fun k ↦ ((-1 : ℤ) ^ i.val) • k)
  let F := (SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  have hδ := SSet.stdSimplex.δ_comp_yonedaEquiv_symm x i
  have hmap := F.congr_map hδ
  rw [Functor.map_comp] at hmap
  have hn := congrArg (fun k ↦ k.f (n + 1)) hmap
  change (SSet.chainComplexMap
        (SSet.stdSimplex.map (SimplexCategory.δ i))
        (AddCommGrpCat.of ℤ)).f (n + 1) ≫
      (SSet.chainComplexMap (SSet.yonedaEquiv.symm x)
        (AddCommGrpCat.of ℤ)).f (n + 1) =
    (SSet.chainComplexMap
      (SSet.yonedaEquiv.symm (X.δ i x))
      (AddCommGrpCat.of ℤ)).f (n + 1) at hn
  calc
    _ = prism n ≫
        ((SSet.chainComplexMap
            (SSet.stdSimplex.map (SimplexCategory.δ i))
            (AddCommGrpCat.of ℤ)).f (n + 1) ≫
          (SSet.chainComplexMap (SSet.yonedaEquiv.symm x)
            (AddCommGrpCat.of ℤ)).f (n + 1)) := Category.assoc _ _ _
    _ = _ := congrArg (fun k ↦ prism n ≫ k) hn

/-- One universal prism equation induces the corresponding operator equation on every
simplicial set in that degree. -/
theorem universalStandardSimplexPrismComponent_boundary_succ
    (prism : ∀ n : ℕ, AddCommGrpCat.of ℤ ⟶
      ((Δ[n] : SSet.{0}).chainComplex
        (AddCommGrpCat.of ℤ)).X (n + 1))
    (n : ℕ)
    (h : SubdivisionBarycentricHomotopy.standardBarycentricLastVertexDiscrepancy (n + 1) =
      prism (n + 1) ≫
          ((Δ[n + 1] : SSet.{0}).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) +
        SubdivisionBarycentricHomotopy.standardPrismFaceChain prism (n + 1))
    (X : SSet.{0}) :
    (barycentricLastVertexDiscrepancyChainMap X).f (n + 1) =
      universalStandardSimplexPrismComponent (n + 1)
          (prism (n + 1)) X ≫
        (X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) +
      (X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n ≫
        universalStandardSimplexPrismComponent n (prism n) X := by
  apply X.chainComplex_hom_ext
  intro x
  simp only [Preadditive.comp_add]
  rw [iota_barycentricLastVertexDiscrepancyChainMap, h,
    Preadditive.add_comp]
  apply congrArg₂ (fun a b ↦ a + b)
  · rw [← Category.assoc, iota_universalStandardSimplexPrismComponent]
    simp only [Category.assoc]
    congr 1
    exact ((SSet.chainComplexMap (SSet.yonedaEquiv.symm x)
      (AddCommGrpCat.of ℤ)).comm (n + 2) (n + 1)).symm
  · exact standardPrismFaceChain_transport_raw prism X n x

/-- Once the prism equation is known in degree `n+1`, the residual used to define the next
prism is a cycle. The cancellation is exactly `∂² = 0`, expressed through the transported
universal prism operator. -/
theorem standardBarycentricLastVertexPrismResidual_cycle_succ
    (prism : ∀ n : ℕ, AddCommGrpCat.of ℤ ⟶
      ((Δ[n] : SSet.{0}).chainComplex
        (AddCommGrpCat.of ℤ)).X (n + 1))
    (n : ℕ)
    (h : SubdivisionBarycentricHomotopy.standardBarycentricLastVertexDiscrepancy (n + 1) =
      prism (n + 1) ≫
          ((Δ[n + 1] : SSet.{0}).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) +
        SubdivisionBarycentricHomotopy.standardPrismFaceChain prism (n + 1)) :
    (SubdivisionBarycentricHomotopy.standardBarycentricLastVertexDiscrepancy (n + 2) -
        SubdivisionBarycentricHomotopy.standardPrismFaceChain prism (n + 2)) ≫
      ((Δ[n + 2] : SSet.{0}).chainComplex
        (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) = 0 := by
  let X : SSet.{0} := (Δ[n + 2] : SSet.{0})
  let K := barycentricLastVertexDiscrepancyChainMap X
  let U := universalStandardSimplexPrismComponent (n + 1)
    (prism (n + 1)) X
  let V := universalStandardSimplexPrismComponent n (prism n) X
  have hop := universalStandardSimplexPrismComponent_boundary_succ
    prism n h X
  have hU : U ≫
      (X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) =
      K.f (n + 1) -
        (X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n ≫ V := by
    dsimp [K, U, V] at hop ⊢
    rw [hop]
    abel
  rw [Preadditive.sub_comp]
  have hface : SubdivisionBarycentricHomotopy.standardPrismFaceChain prism (n + 2) ≫
      (X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) =
      SubdivisionBarycentricHomotopy.standardBarycentricLastVertexDiscrepancy (n + 2) ≫
        (X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) := by
    rw [standardPrismFaceChain_eq_top_boundary_comp]
    change ((X.ιChainComplex (SubdivisionBarycentricHomotopy.standardSimplexTopSimplex (n + 2)) ≫
        (X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1)) ≫ U) ≫
          (X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) = _
    rw [Category.assoc, hU, Preadditive.comp_sub]
    have hdd :
        (X.ιChainComplex (SubdivisionBarycentricHomotopy.standardSimplexTopSimplex (n + 2)) ≫
          (X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1)) ≫
            (X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n = 0 := by
      rw [Category.assoc,
        (X.chainComplex (AddCommGrpCat.of ℤ)).d_comp_d, comp_zero]
    have hddV :
        (X.ιChainComplex (SubdivisionBarycentricHomotopy.standardSimplexTopSimplex (n + 2)) ≫
          (X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1)) ≫
            (X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n ≫ V = 0 := by
      rw [← Category.assoc, hdd, zero_comp]
    rw [hddV, sub_zero, Category.assoc, ← K.comm,
      standardBarycentricLastVertexDiscrepancy_eq_top_comp]
    dsimp [X, K]
    exact (Category.assoc _ _ _).symm
  rw [hface, sub_self]

/-- The universal prism chains obtained recursively by filling each residual with the
zero-vertex cone. -/
noncomputable def canonicalBarycentricLastVertexPrism
    (n : ℕ) : AddCommGrpCat.of ℤ ⟶
      ((Δ[n] : SSet.{0}).chainComplex
        (AddCommGrpCat.of ℤ)).X (n + 1) :=
  match n with
  | 0 => 0
  | n + 1 =>
      (SubdivisionBarycentricHomotopy.standardBarycentricLastVertexDiscrepancy (n + 1) -
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          (canonicalBarycentricLastVertexPrism n ≫
            (SSet.chainComplexMap
              (SSet.stdSimplex.map (SimplexCategory.δ i))
              (AddCommGrpCat.of ℤ)).f (n + 1))) ≫
        standardSimplexZeroConeComponent (n + 1) (n + 1)
termination_by n

@[simp]
theorem canonicalBarycentricLastVertexPrism_zero :
    StandardSimplexCone.canonicalBarycentricLastVertexPrism 0 = 0 := by
  simp [StandardSimplexCone.canonicalBarycentricLastVertexPrism]

/-- The recursive prism is the cone on discrepancy minus the face
prisms. -/
theorem canonicalBarycentricLastVertexPrism_succ
    (n : ℕ) :
    StandardSimplexCone.canonicalBarycentricLastVertexPrism (n + 1) =
      (SubdivisionBarycentricHomotopy.standardBarycentricLastVertexDiscrepancy (n + 1) -
        SubdivisionBarycentricHomotopy.standardPrismFaceChain StandardSimplexCone.canonicalBarycentricLastVertexPrism (n + 1)) ≫
        standardSimplexZeroConeComponent (n + 1) (n + 1) := by
  simp [StandardSimplexCone.canonicalBarycentricLastVertexPrism, SubdivisionBarycentricHomotopy.standardPrismFaceChain]

/-- The first recursive residual is a cycle; both its degree-zero discrepancy and its previous
prism vanish. -/
theorem canonicalBarycentricLastVertexPrismResidual_cycle_one :
    (SubdivisionBarycentricHomotopy.standardBarycentricLastVertexDiscrepancy 1 -
        SubdivisionBarycentricHomotopy.standardPrismFaceChain StandardSimplexCone.canonicalBarycentricLastVertexPrism 1) ≫
      ((Δ[1] : SSet.{0}).chainComplex
        (AddCommGrpCat.of ℤ)).d 1 0 = 0 := by
  rw [Preadditive.sub_comp,
    standardBarycentricLastVertexDiscrepancy_boundary_stdSimplex]
  simp [SubdivisionBarycentricHomotopy.standardPrismFaceChain]

/-- The recursively coned universal chains satisfy the complete universal prism equation in
every degree. -/
theorem canonicalBarycentricLastVertexPrism_boundary
    (n : ℕ) :
    SubdivisionBarycentricHomotopy.standardBarycentricLastVertexDiscrepancy n =
      StandardSimplexCone.canonicalBarycentricLastVertexPrism n ≫
          ((Δ[n] : SSet.{0}).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 1) n +
        SubdivisionBarycentricHomotopy.standardPrismFaceChain StandardSimplexCone.canonicalBarycentricLastVertexPrism n := by
  induction n with
  | zero =>
      simp [SubdivisionBarycentricHomotopy.standardPrismFaceChain]
  | succ n ih =>
      have hcycle :
          (SubdivisionBarycentricHomotopy.standardBarycentricLastVertexDiscrepancy (n + 1) -
              SubdivisionBarycentricHomotopy.standardPrismFaceChain StandardSimplexCone.canonicalBarycentricLastVertexPrism (n + 1)) ≫
            ((Δ[n + 1] : SSet.{0}).chainComplex
              (AddCommGrpCat.of ℤ)).d (n + 1) n = 0 := by
        cases n with
        | zero =>
            exact canonicalBarycentricLastVertexPrismResidual_cycle_one
        | succ k =>
            exact standardBarycentricLastVertexPrismResidual_cycle_succ
              StandardSimplexCone.canonicalBarycentricLastVertexPrism k ih
      have hfill := standardSimplexZeroConeComponent_fills_cycle
        (n + 1) n
        (SubdivisionBarycentricHomotopy.standardBarycentricLastVertexDiscrepancy (n + 1) -
          SubdivisionBarycentricHomotopy.standardPrismFaceChain StandardSimplexCone.canonicalBarycentricLastVertexPrism (n + 1))
        hcycle
      rw [canonicalBarycentricLastVertexPrism_succ, Category.assoc, hfill]
      abel

/-- The explicit canonical chain homotopy from subdivision followed by last vertex to the
identity, built from the recursively coned universal prisms. -/
noncomputable def barycentricSubdivisionLastVertexHomotopyCanonical
    (X : SSet.{0}) :
    Homotopy
      (SubdivisionBarycentricOuterFaces.barycentricSubdivisionChainMapCanonical X ≫
        SubdivisionBasic.subdivisionLastVertexChainMap X)
      (𝟙 (X.chainComplex (AddCommGrpCat.of ℤ))) :=
  SubdivisionBarycentricHomotopy.barycentricSubdivisionLastVertexHomotopy
    { prism := StandardSimplexCone.canonicalBarycentricLastVertexPrism
      boundary := canonicalBarycentricLastVertexPrism_boundary } X

end

end OAI.AlgebraicTopology.Singular.StandardSimplexCone
