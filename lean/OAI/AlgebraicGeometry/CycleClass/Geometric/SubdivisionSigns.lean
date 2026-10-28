import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicGeometry.CycleClass.Geometric.BarycentricSimplex
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology
import OAI.AlgebraicTopology.Cohomology.Singular.ContinuousFormulas
import Mathlib.GroupTheory.Perm.Sign

/-! # Subdivision Signs -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionSigns.Cycles

noncomputable section

/-!
# Interior face cancellation in geometric barycentric subdivision

Adjacent positions in a vertex permutation give the same face after deleting
the intermediate barycenter. Their permutation signs are opposite.
-/

open scoped BigOperators Classical

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

/-- A signed permutation sum cancels when its values are invariant under a fixed
right adjacent swap (or, more generally, any fixed transposition). -/
theorem sum_perm_sign_eq_zero_of_swap_invariant
    {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup M]
    (a b : ι) (hab : a ≠ b) (f : Equiv.Perm ι → M)
    (hf : ∀ σ, f (σ * Equiv.swap a b) = f σ) :
    ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℤ) • f σ = 0 := by
  apply Finset.sum_involution (fun σ _ => σ * Equiv.swap a b)
  · intro σ _
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, hf σ]
    simp
  · intro σ _ _ h
    have hx := congrArg (fun τ : Equiv.Perm ι => τ a) h
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at hx
    exact hab (σ.injective hx).symm
  · intro σ _
    exact Finset.mem_univ _
  · intro σ _
    ext x
    simp

/-- Swapping adjacent positions preserves every initial interval except the
one ending at the first of the two positions. -/
theorem adjacent_swap_le_iff {n : ℕ} (j : Fin (n + 1))
    (k x : Fin (n + 2)) (hk : k ≠ j.castSucc) :
    Equiv.swap j.castSucc j.succ x ≤ k ↔ x ≤ k := by
  have hkval : k.val ≠ j.val := by
    intro h
    exact hk (Fin.ext h)
  by_cases hxa : x = j.castSucc
  · subst x
    rw [Equiv.swap_apply_left]
    change j.val + 1 ≤ k.val ↔ j.val ≤ k.val
    omega
  · by_cases hxb : x = j.succ
    · subst x
      rw [Equiv.swap_apply_right]
      change j.val ≤ k.val ↔ j.val + 1 ≤ k.val
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

/-- All unaffected initial vertex sets of the paired permutation flags agree. -/
theorem permutation_initial_face_swap_eq {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 1))
    (k : Fin (n + 2)) (hk : k ≠ j.castSucc) :
    (Finset.Iic k).map (σ * Equiv.swap j.castSucc j.succ).toEmbedding =
      (Finset.Iic k).map σ.toEmbedding := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hx
    exact Finset.mem_map.mpr
      ⟨Equiv.swap j.castSucc j.succ y,
        Finset.mem_Iic.mpr ((adjacent_swap_le_iff j k y hk).2 (Finset.mem_Iic.mp hy)),
        hxy⟩
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hx
    refine Finset.mem_map.mpr
      ⟨Equiv.swap j.castSucc j.succ y,
        Finset.mem_Iic.mpr ((adjacent_swap_le_iff j k y hk).2 (Finset.mem_Iic.mp hy)), ?_⟩
    simpa only [Equiv.coe_toEmbedding, Equiv.Perm.mul_apply, Equiv.swap_apply_self] using hxy

/-- The omitted barycentric coordinate of the actual standard face map is zero. -/
theorem standardSimplexFace_omitted_coordinate {n : ℕ} (j : Fin (n + 2))
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace j x j = 0 := by
  exact Finsupp.mapDomain_of_notMem_range x.weights j (by simp)

/-- Paired permutation cells have literally the same deleted interior face map. -/
theorem barycentricSubdivisionMap_comp_inner_face_swap {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 1)) :
    (BarycentricSimplex.Cycles.barycentricSubdivisionMap (σ * Equiv.swap j.castSucc j.succ)).comp
        (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace j.castSucc) =
      (BarycentricSimplex.Cycles.barycentricSubdivisionMap σ).comp
        (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace j.castSucc) := by
  apply ContinuousMap.ext
  intro x
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).injective
  funext i
  simp only [ContinuousMap.comp_apply, BarycentricSimplex.Cycles.barycentricSubdivisionMap,
    BarycentricSimplex.Cycles.BarycentricFlag.toContinuousMap, BarycentricSimplex.Cycles.simplexVertexMap_apply]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k = j.castSucc
  · subst k
    rw [standardSimplexFace_omitted_coordinate]
    simp only [zero_mul]
  · simp only [BarycentricSimplex.Cycles.permutationBarycentricFlag, BarycentricSimplex.Cycles.faceBarycenter_apply]
    rw [permutation_initial_face_swap_eq σ j k hk]

/-- The actual integral singular-chain contribution of any fixed interior face
cancels when summed over all barycentric cells. -/
theorem sum_subdivision_inner_faces_eq_zero {X : Type*} [TopologicalSpace X] {n : ℕ}
    (f : C(Convexity.StdSimplex ℝ (Fin (n + 2)), X)) (j : Fin (n + 1)) :
    (∑ σ : Equiv.Perm (Fin (n + 2)), (Equiv.Perm.sign σ : ℤ) •
      Finsupp.single
        (f.comp ((BarycentricSimplex.Cycles.barycentricSubdivisionMap σ).comp
          (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace j.castSucc))) (1 : ℤ)) = 0 := by
  apply sum_perm_sign_eq_zero_of_swap_invariant j.castSucc j.succ
    (ne_of_lt j.castSucc_lt_succ)
  intro σ
  rw [barycentricSubdivisionMap_comp_inner_face_swap σ j]

/-- The equivalent coefficient-on-generator form matches the usual subdivision
operator on finitely supported integral singular chains. -/
theorem sum_subdivision_inner_face_coefficients_eq_zero
    {X : Type*} [TopologicalSpace X] {n : ℕ}
    (f : C(Convexity.StdSimplex ℝ (Fin (n + 2)), X)) (j : Fin (n + 1)) :
    (∑ σ : Equiv.Perm (Fin (n + 2)),
      Finsupp.single
        (f.comp ((BarycentricSimplex.Cycles.barycentricSubdivisionMap σ).comp
          (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace j.castSucc)))
        (Equiv.Perm.sign σ : ℤ)) = 0 := by
  simpa only [Finsupp.smul_single, smul_eq_mul, mul_one] using
    sum_subdivision_inner_faces_eq_zero f j

/-- Including the alternating boundary coefficient leaves each interior-face
sum zero, in the precise coefficients used by the singular boundary. -/
theorem sum_subdivision_inner_boundary_coefficients_eq_zero
    {X : Type*} [TopologicalSpace X] {n : ℕ}
    (f : C(Convexity.StdSimplex ℝ (Fin (n + 2)), X)) (j : Fin (n + 1)) :
    (∑ σ : Equiv.Perm (Fin (n + 2)),
      Finsupp.single
        (f.comp ((BarycentricSimplex.Cycles.barycentricSubdivisionMap σ).comp
          (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace j.castSucc)))
        ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ j.val)) = 0 := by
  have h : (∑ σ : Equiv.Perm (Fin (n + 2)), (Equiv.Perm.sign σ : ℤ) •
      Finsupp.single
        (f.comp ((BarycentricSimplex.Cycles.barycentricSubdivisionMap σ).comp
          (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace j.castSucc)))
        ((-1 : ℤ) ^ j.val)) = 0 := by
    apply sum_perm_sign_eq_zero_of_swap_invariant j.castSucc j.succ
      (ne_of_lt j.castSucc_lt_succ)
    intro σ
    rw [barycentricSubdivisionMap_comp_inner_face_swap σ j]
  simpa only [Finsupp.smul_single, smul_eq_mul] using h

/-- The total interior part of the boundary of a subdivided singular simplex vanishes. -/
theorem sum_subdivision_all_inner_boundary_coefficients_eq_zero
    {X : Type*} [TopologicalSpace X] {n : ℕ}
    (f : C(Convexity.StdSimplex ℝ (Fin (n + 2)), X)) :
    (∑ j : Fin (n + 1), ∑ σ : Equiv.Perm (Fin (n + 2)),
      Finsupp.single
        (f.comp ((BarycentricSimplex.Cycles.barycentricSubdivisionMap σ).comp
          (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace j.castSucc)))
        ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ j.val)) = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact sum_subdivision_inner_boundary_coefficients_eq_zero f j

/-- The same cancellation holds inside mathlib's actual integral singular chain
complex, including the alternating boundary coefficient. -/
theorem sum_actual_subdivision_inner_faces_eq_zero (X : TopCat.{0}) {n : ℕ}
    (f : C(Convexity.StdSimplex ℝ (Fin (n + 2)), X)) (j : Fin (n + 1)) :
    (∑ σ : Equiv.Perm (Fin (n + 2)), (Equiv.Perm.sign σ : ℤ) •
      (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
        ((AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n).symm
          (f.comp ((BarycentricSimplex.Cycles.barycentricSubdivisionMap σ).comp
            (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace j.castSucc))))
        ((-1 : ℤ) ^ j.val) : (LocalHomology.Cycles.integralSingularChains X).X n) = 0 := by
  apply sum_perm_sign_eq_zero_of_swap_invariant j.castSucc j.succ
    (ne_of_lt j.castSucc_lt_succ)
  intro σ
  rw [barycentricSubdivisionMap_comp_inner_face_swap σ j]

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionSigns.Cycles
