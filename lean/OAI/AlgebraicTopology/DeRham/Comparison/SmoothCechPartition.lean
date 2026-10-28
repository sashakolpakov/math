import OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech
import OAI.AlgebraicTopology.DeRham.Comparison.PartitionFormOperators

/-! # Smooth Cech Partition -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechPartition

noncomputable section

/-!
# Partition homotopy for the actual smooth-form Čech complex

The homotopy inserts one cover index, multiplies by the associated smooth
partition function, and extends by zero. All operators act on actual smooth
forms on open intersections. The identities below are proved from their
pointwise values and the genuine partition-of-unity identity.
-/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff BigOperators

universe u

variable {E ι : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (cover : ι → Opens E) (p : ℕ)

/-- A single Čech coface is restriction after omitting one index. -/
def smoothCechCoface (n : ℕ) (j : Fin (n + 2)) :
    SmoothCech.SmoothCechCochain cover p n →ₗ[ℂ] SmoothCech.SmoothCechCochain cover p (n + 1) :=
  SmoothCech.cechPrecomp (Analysis.DifferentialForms.Manifold.Presheaf.smoothFormPresheaf E p) cover j.succAbove

@[simp]
theorem smoothCechCoface_apply (n : ℕ) (j : Fin (n + 2))
    (c : SmoothCech.SmoothCechCochain cover p n) (a : Fin (n + 2) → ι) :
    smoothCechCoface cover p n j c a =
      Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (SmoothCech.cechIntersection_le_precomp cover a j.succAbove)
        (c (a ∘ j.succAbove)) := rfl

/-- Equal index tuples give equal restricted sections on every common domain. -/
theorem smoothCechSection_congr (n : ℕ) (c : SmoothCech.SmoothCechCochain cover p n)
    {a b : Fin (n + 1) → ι} (hab : a = b) (W : Opens E)
    (hWa : W ≤ SmoothCech.cechIntersection cover a) (hWb : W ≤ SmoothCech.cechIntersection cover b) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hWa (c a) = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hWb (c b) := by
  subst b
  rfl

/-- The Čech differential is the alternating sum of its actual cofaces. -/
theorem smoothCechDelta_eq_sum_coface (n : ℕ) (c : SmoothCech.SmoothCechCochain cover p n) :
    SmoothCech.smoothCechDelta cover p n c =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • smoothCechCoface cover p n j c := by
  funext a
  exact (SmoothCech.smoothCechDelta_apply cover p n c a).trans (by
    simp only [Finset.sum_apply, Pi.smul_apply, smoothCechCoface_apply]
    rfl)

variable (rho : SmoothPartitionOfUnity ι 𝓘(ℝ, E) E (Set.univ : Set E))
  (hsub : rho.IsSubordinate (fun i => (cover i : Set E)))

/-- One weighted insertion, including the proved smooth extension across its boundary. -/
def smoothCechWeightedInsertion (n : ℕ) (i : ι) :
    SmoothCech.SmoothCechCochain cover p (n + 1) →ₗ[ℂ] SmoothCech.SmoothCechCochain cover p n where
  toFun c a := PartitionFormOperators.partitionFormOperator cover rho hsub (SmoothCech.cechIntersection cover a) i
    (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (le_of_eq (SmoothCech.cechIntersection_cons cover i a).symm)
      (c (Fin.cons i a)))
  map_add' c d := by
    funext a
    exact ((PartitionFormOperators.partitionFormOperator cover rho hsub (SmoothCech.cechIntersection cover a) i).comp
      (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (le_of_eq (SmoothCech.cechIntersection_cons cover i a).symm))).map_add
        (c (Fin.cons i a)) (d (Fin.cons i a))
  map_smul' z c := by
    funext a
    exact ((PartitionFormOperators.partitionFormOperator cover rho hsub (SmoothCech.cechIntersection cover a) i).comp
      (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (le_of_eq (SmoothCech.cechIntersection_cons cover i a).symm))).map_smul
        z (c (Fin.cons i a))

theorem smoothCechWeightedInsertion_apply_of_mem (n : ℕ) (i : ι)
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) (a : Fin (n + 1) → ι)
    (x : SmoothCech.cechIntersection cover a) (hxi : (x : E) ∈ cover i) :
    PartitionFormOperators.openFormEvaluation x (smoothCechWeightedInsertion cover p rho hsub n i c a) =
      rho i x • PartitionFormOperators.openFormEvaluation
        (⟨(x : E), (le_of_eq (SmoothCech.cechIntersection_cons cover i a).symm)
          ⟨hxi, x.property⟩⟩ : SmoothCech.cechIntersection cover (Fin.cons i a))
        (c (Fin.cons i a)) := by
  exact PartitionFormOperators.supportedFormExtension_apply_of_mem (rho i) (rho i).contMDiff.contDiff
    (hsub i) _ x hxi

theorem smoothCechWeightedInsertion_apply_of_notMem (n : ℕ) (i : ι)
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) (a : Fin (n + 1) → ι)
    (x : SmoothCech.cechIntersection cover a) (hxi : (x : E) ∉ cover i) :
    PartitionFormOperators.openFormEvaluation x (smoothCechWeightedInsertion cover p rho hsub n i c a) = 0 := by
  exact PartitionFormOperators.supportedFormExtension_apply_of_notMem (rho i) (rho i).contMDiff.contDiff
    (hsub i) _ x hxi

/-- Inserting the index omitted by the zeroth coface gives the usual partition operator. -/
theorem smoothCechWeightedInsertion_coface_zero (n : ℕ) (i : ι)
    (c : SmoothCech.SmoothCechCochain cover p n) (a : Fin (n + 1) → ι) :
    smoothCechWeightedInsertion cover p rho hsub n i
        (smoothCechCoface cover p n 0 c) a =
      PartitionFormOperators.partitionFormOperator cover rho hsub (SmoothCech.cechIntersection cover a) i
        (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict inf_le_right (c a)) := by
  change ((a : Fin (n + 1) → ι) → Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (SmoothCech.cechIntersection cover a) p) at c
  change PartitionFormOperators.partitionFormOperator cover rho hsub (SmoothCech.cechIntersection cover a) i
    (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (le_of_eq (SmoothCech.cechIntersection_cons cover i a).symm)
      (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict
        (SmoothCech.cechIntersection_le_precomp cover (Fin.cons i a) Fin.succ)
        (c (Fin.cons i a ∘ Fin.succ)))) = _
  simp only [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_trans]
  apply congrArg
  exact smoothCechSection_congr cover p n c (Fin.cons_comp_succ i a) _ _ _

/-- Restriction of a weighted insertion agrees with omitting any later inserted index. -/
theorem smoothCechWeightedInsertion_coface_succ (n : ℕ) (i : ι) (j : Fin (n + 2))
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) :
    smoothCechWeightedInsertion cover p rho hsub (n + 1) i
        (smoothCechCoface cover p (n + 1) j.succ c) =
      smoothCechCoface cover p n j
        (smoothCechWeightedInsertion cover p rho hsub n i c) := by
  change ((a : Fin (n + 2) → ι) → Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (SmoothCech.cechIntersection cover a) p) at c
  funext a
  change PartitionFormOperators.supportedFormExtension (rho i) (rho i).contMDiff.contDiff (hsub i)
      (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (le_of_eq (SmoothCech.cechIntersection_cons cover i a).symm)
        (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict
          (SmoothCech.cechIntersection_le_precomp cover (Fin.cons i a) j.succ.succAbove)
          (c (Fin.cons i a ∘ j.succ.succAbove)))) =
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (SmoothCech.cechIntersection_le_precomp cover a j.succAbove)
      (PartitionFormOperators.supportedFormExtension (rho i) (rho i).contMDiff.contDiff (hsub i)
        (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict
          (le_of_eq (SmoothCech.cechIntersection_cons cover i (a ∘ j.succAbove)).symm)
          (c (Fin.cons i (a ∘ j.succAbove)))))
  rw [PartitionFormOperators.supportedFormExtension_restrict]
  simp only [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_trans]
  apply congrArg
  exact smoothCechSection_congr cover p (n + 1) c
    (Fin.cons_comp_succ_succAbove i a j) _ _ _

variable [Fintype ι]

/-- The finite smooth-partition homotopy on actual Čech cochains. -/
def smoothCechHomotopy (n : ℕ) :
    SmoothCech.SmoothCechCochain cover p (n + 1) →ₗ[ℂ] SmoothCech.SmoothCechCochain cover p n :=
  ∑ i, smoothCechWeightedInsertion cover p rho hsub n i

theorem smoothCechHomotopy_eq_sum (n : ℕ)
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) :
    smoothCechHomotopy cover p rho hsub n c =
      ∑ i, smoothCechWeightedInsertion cover p rho hsub n i c := by
  exact LinearMap.sum_apply _ _ _

/-- The zeroth coface is a right inverse to the partition homotopy. -/
theorem smoothCechHomotopy_coface_zero (n : ℕ) (c : SmoothCech.SmoothCechCochain cover p n) :
    smoothCechHomotopy cover p rho hsub n (smoothCechCoface cover p n 0 c) = c := by
  funext a
  have h1 : smoothCechHomotopy cover p rho hsub n (smoothCechCoface cover p n 0 c) a =
      ∑ i, smoothCechWeightedInsertion cover p rho hsub n i
        (smoothCechCoface cover p n 0 c) a := by
    rw [smoothCechHomotopy_eq_sum, Finset.sum_apply]
  have h2 : (∑ i, smoothCechWeightedInsertion cover p rho hsub n i
        (smoothCechCoface cover p n 0 c) a) =
      ∑ i, PartitionFormOperators.partitionFormOperator cover rho hsub (SmoothCech.cechIntersection cover a) i
        (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict inf_le_right (c a)) := by
    exact Finset.sum_congr rfl (fun i _ =>
      smoothCechWeightedInsertion_coface_zero cover p rho hsub n i c a)
  exact h1.trans (h2.trans (PartitionFormOperators.sum_partitionFormOperator cover rho hsub
    (SmoothCech.cechIntersection cover a) (Set.subset_univ _) (c a)))

/-- Later cofaces commute with partition insertion after shifting their index. -/
theorem smoothCechHomotopy_coface_succ (n : ℕ) (j : Fin (n + 2))
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) :
    smoothCechHomotopy cover p rho hsub (n + 1)
        (smoothCechCoface cover p (n + 1) j.succ c) =
      smoothCechCoface cover p n j (smoothCechHomotopy cover p rho hsub n c) := by
  rw [smoothCechHomotopy_eq_sum, smoothCechHomotopy_eq_sum, map_sum]
  exact Finset.sum_congr rfl (fun i _ =>
    smoothCechWeightedInsertion_coface_succ cover p rho hsub n i j c)

/-- Splitting off the zeroth coface gives the signed homotopy identity. -/
theorem smoothCechHomotopy_delta (n : ℕ) (c : SmoothCech.SmoothCechCochain cover p (n + 1)) :
    smoothCechHomotopy cover p rho hsub (n + 1) (SmoothCech.smoothCechDelta cover p (n + 1) c) =
      c - SmoothCech.smoothCechDelta cover p n (smoothCechHomotopy cover p rho hsub n c) := by
  rw [smoothCechDelta_eq_sum_coface, map_sum]
  simp only [map_zsmul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    smoothCechHomotopy_coface_zero, smoothCechHomotopy_coface_succ]
  rw [sub_eq_add_neg, smoothCechDelta_eq_sum_coface, ← Finset.sum_neg_distrib]
  apply congrArg (fun z => c + z)
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ, mul_smul, neg_one_smul, smul_neg]

/-- The actual partition operator contracts the Čech complex in every positive degree. -/
theorem smoothCech_contraction (n : ℕ) (c : SmoothCech.SmoothCechCochain cover p (n + 1)) :
    SmoothCech.smoothCechDelta cover p n (smoothCechHomotopy cover p rho hsub n c) +
      smoothCechHomotopy cover p rho hsub (n + 1) (SmoothCech.smoothCechDelta cover p (n + 1) c) =
        c := by
  rw [smoothCechHomotopy_delta]
  abel

/-- A positive-degree cocycle has the explicit primitive supplied by the partition. -/
theorem smoothCechDelta_homotopy_of_cycle (n : ℕ)
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) (hc : SmoothCech.smoothCechDelta cover p (n + 1) c = 0) :
    SmoothCech.smoothCechDelta cover p n (smoothCechHomotopy cover p rho hsub n c) = c := by
  have h := smoothCech_contraction cover p rho hsub n c
  rw [hc, map_zero, add_zero] at h
  exact h

include rho hsub in
/-- The genuine smooth-form Čech complex is exact in positive degrees for a finite partition. -/
theorem smoothCechDelta_range_eq_ker (n : ℕ) :
    LinearMap.range (SmoothCech.smoothCechDelta cover p n) =
      LinearMap.ker (SmoothCech.smoothCechDelta cover p (n + 1)) := by
  apply le_antisymm
  · rintro c ⟨b, rfl⟩
    exact SmoothCech.smoothCechDelta_squared cover p n b
  · intro c hc
    exact ⟨smoothCechHomotopy cover p rho hsub n c,
      smoothCechDelta_homotopy_of_cycle cover p rho hsub n c hc⟩

/-- A finite open cover of a finite-dimensional real normed space has exact smooth Čech rows. -/
theorem smoothCechDelta_range_eq_ker_of_cover [FiniteDimensional ℝ E]
    (hcover : ∀ x : E, ∃ i, x ∈ cover i) (n : ℕ) :
    LinearMap.range (SmoothCech.smoothCechDelta cover p n) =
      LinearMap.ker (SmoothCech.smoothCechDelta cover p (n + 1)) := by
  obtain ⟨partition, hpartition⟩ := PartitionFormOperators.exists_subordinateSmoothPartition cover hcover
  exact smoothCechDelta_range_eq_ker cover p partition hpartition n

end

end OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechPartition
