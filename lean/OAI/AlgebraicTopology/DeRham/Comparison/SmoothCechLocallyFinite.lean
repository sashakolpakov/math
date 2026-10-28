import OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechPartition
import OAI.Analysis.DifferentialForms.Manifold.OpenLocallyFiniteSum

/-! # Smooth Cech Locally Finite -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechLocallyFinite

noncomputable section

/-!
# Locally finite partition homotopies for genuine smooth Čech cochains

The index set is arbitrary. Local finiteness is proved from the supports of
the actual smooth partition functions, then used to sum the actual smooth
weighted insertions on each open intersection.
-/

open _root_.TopologicalSpace Function
open scoped _root_.Manifold ContDiff BigOperators

universe u

variable {E ι : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (cover : ι → Opens E) (p : ℕ)

/-- Evaluation of a genuine Čech section at a point of its open intersection. -/
def smoothCechEvaluation (n : ℕ) (a : Fin (n + 1) → ι)
    (x : SmoothCech.cechIntersection cover a) : SmoothCech.SmoothCechCochain cover p n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Basic.FormValue E p where
  toFun c := PartitionFormOperators.openFormEvaluation x (c a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Point evaluation of a coface is evaluation of the original restricted section. -/
theorem smoothCechEvaluation_coface (n : ℕ) (j : Fin (n + 2))
    (a : Fin (n + 2) → ι) (x : SmoothCech.cechIntersection cover a)
    (c : SmoothCech.SmoothCechCochain cover p n) :
    smoothCechEvaluation cover p (n + 1) a x (SmoothCechPartition.smoothCechCoface cover p n j c) =
      smoothCechEvaluation cover p n (a ∘ j.succAbove)
        ⟨(x : E), SmoothCech.cechIntersection_le_precomp cover a j.succAbove x.property⟩ c := rfl

variable (rho : SmoothPartitionOfUnity ι 𝓘(ℝ, E) E (Set.univ : Set E))
  (hsub : rho.IsSubordinate (fun i => (cover i : Set E)))

/-- A weighted insertion can be nonzero only where its actual partition function is nonzero. -/
theorem smoothCechWeightedInsertion_support_subset (n : ℕ) (i : ι)
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) (a : Fin (n + 1) → ι) :
    support (fun x : SmoothCech.cechIntersection cover a =>
      smoothCechEvaluation cover p n a x (SmoothCechPartition.smoothCechWeightedInsertion cover p rho hsub n i c)) ⊆
        support (fun x : SmoothCech.cechIntersection cover a => rho i x) := by
  intro x hx
  change rho i x ≠ 0
  intro hz
  apply hx
  change rho i x •
    (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (le_of_eq (SmoothCech.cechIntersection_cons cover i a).symm)
      (c (Fin.cons i a))).extension x = 0
  rw [hz]
  exact zero_smul ℝ
    ((Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (n := p)
      (le_of_eq (SmoothCech.cechIntersection_cons cover i a).symm) (c (Fin.cons i a))).extension (x : E))

/-- The weighted insertions form a locally finite family on each actual open intersection. -/
theorem smoothCechWeightedInsertion_locallyFinite (n : ℕ)
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) (a : Fin (n + 1) → ι) :
    LocallyFinite (fun i => support (fun x : SmoothCech.cechIntersection cover a =>
      smoothCechEvaluation cover p n a x
        (SmoothCechPartition.smoothCechWeightedInsertion cover p rho hsub n i c))) := by
  exact (rho.locallyFinite.preimage_continuous continuous_subtype_val).subset
    (fun i => smoothCechWeightedInsertion_support_subset cover p rho hsub n i c a)

/-- At a point only finitely many weighted insertions contribute. -/
theorem smoothCechWeightedInsertion_finite_support (n : ℕ)
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) (a : Fin (n + 1) → ι)
    (x : SmoothCech.cechIntersection cover a) :
    HasFiniteSupport (fun i => smoothCechEvaluation cover p n a x
      (SmoothCechPartition.smoothCechWeightedInsertion cover p rho hsub n i c)) :=
  (smoothCechWeightedInsertion_locallyFinite cover p rho hsub n c a).point_finite x

/-- The pointwise locally finite sum of the proved smooth weighted insertions. -/
def smoothCechLocallyFiniteInsertion (n : ℕ)
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) : SmoothCech.SmoothCechCochain cover p n :=
  fun a => Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.locallyFiniteSum
    (fun i => SmoothCechPartition.smoothCechWeightedInsertion cover p rho hsub n i c a)
    (smoothCechWeightedInsertion_locallyFinite cover p rho hsub n c a)

theorem smoothCechLocallyFiniteInsertion_apply (n : ℕ)
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) (a : Fin (n + 1) → ι)
    (x : SmoothCech.cechIntersection cover a) :
    smoothCechEvaluation cover p n a x (smoothCechLocallyFiniteInsertion cover p rho hsub n c) =
      ∑ᶠ i, smoothCechEvaluation cover p n a x
        (SmoothCechPartition.smoothCechWeightedInsertion cover p rho hsub n i c) :=
  Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.locallyFiniteSum_apply
    (fun i => SmoothCechPartition.smoothCechWeightedInsertion cover p rho hsub n i c a)
    (smoothCechWeightedInsertion_locallyFinite cover p rho hsub n c a) x

theorem smoothCechLocallyFiniteInsertion_add (n : ℕ)
    (c d : SmoothCech.SmoothCechCochain cover p (n + 1)) :
    smoothCechLocallyFiniteInsertion cover p rho hsub n (c + d) =
      smoothCechLocallyFiniteInsertion cover p rho hsub n c +
        smoothCechLocallyFiniteInsertion cover p rho hsub n d := by
  funext a
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  change smoothCechEvaluation cover p n a x
      (smoothCechLocallyFiniteInsertion cover p rho hsub n (c + d)) =
    smoothCechEvaluation cover p n a x (smoothCechLocallyFiniteInsertion cover p rho hsub n c) +
      smoothCechEvaluation cover p n a x (smoothCechLocallyFiniteInsertion cover p rho hsub n d)
  rw [smoothCechLocallyFiniteInsertion_apply, smoothCechLocallyFiniteInsertion_apply,
    smoothCechLocallyFiniteInsertion_apply]
  exact (finsum_congr (fun i => ((smoothCechEvaluation cover p n a x).comp
    (SmoothCechPartition.smoothCechWeightedInsertion cover p rho hsub n i)).map_add c d)).trans
      (finsum_add_distrib
        (smoothCechWeightedInsertion_finite_support cover p rho hsub n c a x)
        (smoothCechWeightedInsertion_finite_support cover p rho hsub n d a x))

theorem smoothCechLocallyFiniteInsertion_smul (n : ℕ) (z : ℂ)
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) :
    smoothCechLocallyFiniteInsertion cover p rho hsub n (z • c) =
      z • smoothCechLocallyFiniteInsertion cover p rho hsub n c := by
  funext a
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  change smoothCechEvaluation cover p n a x
      (smoothCechLocallyFiniteInsertion cover p rho hsub n (z • c)) =
    z • smoothCechEvaluation cover p n a x (smoothCechLocallyFiniteInsertion cover p rho hsub n c)
  rw [smoothCechLocallyFiniteInsertion_apply, smoothCechLocallyFiniteInsertion_apply]
  exact (finsum_congr (fun i => ((smoothCechEvaluation cover p n a x).comp
    (SmoothCechPartition.smoothCechWeightedInsertion cover p rho hsub n i)).map_smul z c)).trans
      (smul_finsum' z
        (smoothCechWeightedInsertion_finite_support cover p rho hsub n c a x)).symm

/-- The locally finite partition operator is genuinely complex-linear. -/
def smoothCechLocallyFiniteHomotopy (n : ℕ) :
    SmoothCech.SmoothCechCochain cover p (n + 1) →ₗ[ℂ] SmoothCech.SmoothCechCochain cover p n where
  toFun := smoothCechLocallyFiniteInsertion cover p rho hsub n
  map_add' := smoothCechLocallyFiniteInsertion_add cover p rho hsub n
  map_smul' := smoothCechLocallyFiniteInsertion_smul cover p rho hsub n

theorem smoothCechLocallyFiniteHomotopy_apply (n : ℕ)
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) (a : Fin (n + 1) → ι)
    (x : SmoothCech.cechIntersection cover a) :
    smoothCechEvaluation cover p n a x (smoothCechLocallyFiniteHomotopy cover p rho hsub n c) =
      ∑ᶠ i, smoothCechEvaluation cover p n a x
        (SmoothCechPartition.smoothCechWeightedInsertion cover p rho hsub n i c) :=
  smoothCechLocallyFiniteInsertion_apply cover p rho hsub n c a x

/-- The pointwise partition identity gives the zeroth coface identity without finiteness. -/
theorem smoothCechLocallyFiniteHomotopy_coface_zero (n : ℕ)
    (c : SmoothCech.SmoothCechCochain cover p n) :
    smoothCechLocallyFiniteHomotopy cover p rho hsub n (SmoothCechPartition.smoothCechCoface cover p n 0 c) = c := by
  funext a
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  change smoothCechEvaluation cover p n a x
      (smoothCechLocallyFiniteHomotopy cover p rho hsub n (SmoothCechPartition.smoothCechCoface cover p n 0 c)) =
    smoothCechEvaluation cover p n a x c
  rw [smoothCechLocallyFiniteHomotopy_apply]
  have hterm (i : ι) : smoothCechEvaluation cover p n a x
      (SmoothCechPartition.smoothCechWeightedInsertion cover p rho hsub n i (SmoothCechPartition.smoothCechCoface cover p n 0 c)) =
        rho i x • smoothCechEvaluation cover p n a x c := by
    exact (congrArg (PartitionFormOperators.openFormEvaluation x)
      (SmoothCechPartition.smoothCechWeightedInsertion_coface_zero cover p rho hsub n i c a)).trans
        (PartitionFormOperators.partitionFormOperator_restricted_apply cover rho hsub (SmoothCech.cechIntersection cover a) i (c a) x)
  rw [finsum_congr hterm,
    ← finsum_smul' (rho.locallyFinite.point_finite (x : E)),
    rho.sum_eq_one (Set.mem_univ (x : E)), one_smul]

/-- The locally finite sum commutes with the later cofaces by pointwise restriction. -/
theorem smoothCechLocallyFiniteHomotopy_coface_succ (n : ℕ) (j : Fin (n + 2))
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) :
    smoothCechLocallyFiniteHomotopy cover p rho hsub (n + 1)
        (SmoothCechPartition.smoothCechCoface cover p (n + 1) j.succ c) =
      SmoothCechPartition.smoothCechCoface cover p n j (smoothCechLocallyFiniteHomotopy cover p rho hsub n c) := by
  funext a
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  change smoothCechEvaluation cover p (n + 1) a x
      (smoothCechLocallyFiniteHomotopy cover p rho hsub (n + 1)
        (SmoothCechPartition.smoothCechCoface cover p (n + 1) j.succ c)) =
    smoothCechEvaluation cover p (n + 1) a x
      (SmoothCechPartition.smoothCechCoface cover p n j (smoothCechLocallyFiniteHomotopy cover p rho hsub n c))
  rw [smoothCechLocallyFiniteHomotopy_apply, smoothCechEvaluation_coface,
    smoothCechLocallyFiniteHomotopy_apply]
  apply finsum_congr
  intro i
  exact (congrArg (smoothCechEvaluation cover p (n + 1) a x)
    (SmoothCechPartition.smoothCechWeightedInsertion_coface_succ cover p rho hsub n i j c)).trans
      (smoothCechEvaluation_coface cover p n j a x
        (SmoothCechPartition.smoothCechWeightedInsertion cover p rho hsub n i c))

/-- Signed cancellation for the actual arbitrary-index partition homotopy. -/
theorem smoothCechLocallyFiniteHomotopy_delta (n : ℕ)
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) :
    smoothCechLocallyFiniteHomotopy cover p rho hsub (n + 1)
        (SmoothCech.smoothCechDelta cover p (n + 1) c) =
      c - SmoothCech.smoothCechDelta cover p n (smoothCechLocallyFiniteHomotopy cover p rho hsub n c) := by
  rw [SmoothCechPartition.smoothCechDelta_eq_sum_coface, map_sum]
  simp only [map_zsmul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    smoothCechLocallyFiniteHomotopy_coface_zero, smoothCechLocallyFiniteHomotopy_coface_succ]
  rw [sub_eq_add_neg, SmoothCechPartition.smoothCechDelta_eq_sum_coface, ← Finset.sum_neg_distrib]
  apply congrArg (fun z => c + z)
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ, mul_smul, neg_one_smul, smul_neg]

/-- Actual positive-degree Čech contraction with no finite-index hypothesis. -/
theorem smoothCechLocallyFinite_contraction (n : ℕ)
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) :
    SmoothCech.smoothCechDelta cover p n (smoothCechLocallyFiniteHomotopy cover p rho hsub n c) +
      smoothCechLocallyFiniteHomotopy cover p rho hsub (n + 1)
        (SmoothCech.smoothCechDelta cover p (n + 1) c) = c := by
  rw [smoothCechLocallyFiniteHomotopy_delta]
  abel

/-- The locally finite operator explicitly supplies a primitive of every positive cocycle. -/
theorem smoothCechLocallyFiniteDelta_homotopy_of_cycle (n : ℕ)
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) (hc : SmoothCech.smoothCechDelta cover p (n + 1) c = 0) :
    SmoothCech.smoothCechDelta cover p n (smoothCechLocallyFiniteHomotopy cover p rho hsub n c) = c := by
  have h := smoothCechLocallyFinite_contraction cover p rho hsub n c
  rw [hc, map_zero, add_zero] at h
  exact h

include rho hsub in
/-- Positive-degree exactness follows from the constructed locally finite partition operator. -/
theorem smoothCechLocallyFiniteDelta_range_eq_ker (n : ℕ) :
    LinearMap.range (SmoothCech.smoothCechDelta cover p n) =
      LinearMap.ker (SmoothCech.smoothCechDelta cover p (n + 1)) := by
  apply le_antisymm
  · rintro c ⟨b, rfl⟩
    exact SmoothCech.smoothCechDelta_squared cover p n b
  · intro c hc
    exact ⟨smoothCechLocallyFiniteHomotopy cover p rho hsub n c,
      smoothCechLocallyFiniteDelta_homotopy_of_cycle cover p rho hsub n c hc⟩

/-- Every open cover of the whole finite-dimensional normed space has exact smooth Čech rows. -/
theorem smoothCechDelta_range_eq_ker_of_arbitrary_cover [FiniteDimensional ℝ E]
    (hcover : ∀ x : E, ∃ i, x ∈ cover i) (n : ℕ) :
    LinearMap.range (SmoothCech.smoothCechDelta cover p n) =
      LinearMap.ker (SmoothCech.smoothCechDelta cover p (n + 1)) := by
  obtain ⟨partition, hpartition⟩ := PartitionFormOperators.exists_subordinateSmoothPartition cover hcover
  exact smoothCechLocallyFiniteDelta_range_eq_ker cover p partition hpartition n

end

end OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechLocallyFinite
