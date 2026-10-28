import OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech
import OAI.Analysis.DifferentialForms.Manifold.ManifoldSheaf
import OAI.Analysis.DifferentialForms.Manifold.RelativeExtension
import OAI.Analysis.DifferentialForms.Manifold.CechContractionAlgebra
import OAI.Analysis.DifferentialForms.Manifold.FinitePartition

/-! # Cech Contraction -/

namespace OAI.Analysis.DifferentialForms.Manifold.CechContraction

noncomputable section

/-!
An explicit finite Čech contraction for the genuine sheaf of smooth manifold
forms. The operator multiplies by a subordinate smooth partition and extends
from each prefixed intersection. The homotopy identity is proved on actual
sections, using their values on tangent vectors at each point.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite Set
open scoped _root_.Manifold ContDiff BigOperators

universe u

open OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech

variable {E M ι : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- Čech cochains with values in actual smooth manifold differential forms. -/
abbrev ManifoldCechCochain (U : ι → Opens M) (p n : ℕ) :=
  (a : Fin (n + 1) → ι) → Open.SmoothOpenManifoldForm E (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) p

/-- The signed restriction differential of the genuine manifold-form sheaf. -/
abbrev manifoldCechDelta (U : ι → Opens M) (p n : ℕ) :
    ManifoldCechCochain (E := E) U p n →ₗ[ℂ]
      ManifoldCechCochain (E := E) U p (n + 1) :=
  AlgebraicTopology.DeRham.Comparison.SmoothCech.cechDelta (ManifoldSheaf.manifoldFormPresheaf E M p) U n

/-- The actual categorical Čech complex of the manifold-form sheaf. -/
abbrev manifoldCechComplex (U : ι → Opens M) (p : ℕ) :=
  AlgebraicTopology.DeRham.Comparison.SmoothCech.cechComplex (ManifoldSheaf.manifoldFormPresheaf E M p) U

theorem manifoldCechComplex_d (U : ι → Opens M) (p n : ℕ) :
    (manifoldCechComplex (E := E) U p).d n (n + 1) =
      ModuleCat.ofHom (manifoldCechDelta (E := E) U p n) :=
  AlgebraicTopology.DeRham.Comparison.SmoothCech.cechComplex_d (ManifoldSheaf.manifoldFormPresheaf E M p) U n

theorem manifoldCechDelta_squared (U : ι → Opens M) (p n : ℕ)
    (c : ManifoldCechCochain (E := E) U p n) :
    manifoldCechDelta U p (n + 1) (manifoldCechDelta U p n c) = 0 :=
  AlgebraicTopology.DeRham.Comparison.SmoothCech.cechDelta_squared (ManifoldSheaf.manifoldFormPresheaf E M p) U n c

private def openFormEvaluation {U : Opens M} {p : ℕ} (x : U) :
    Open.SmoothOpenManifoldForm E U p →ₗ[ℂ]
      TangentSpace 𝓘(ℝ, E) (x : M) [⋀^Fin p]→L[ℝ] ℂ where
  toFun form := form x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The categorical Čech differential is the usual alternating restriction
sum on the concrete manifold-form sections. -/
theorem manifoldCechDelta_sections (U : ι → Opens M) (p n : ℕ)
    (c : ManifoldCechCochain (E := E) U p n) (a : Fin (n + 2) → ι) :
    manifoldCechDelta U p n c a =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
        Open.SmoothOpenManifoldForm.restrict (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a j.succAbove)
          (c (a ∘ j.succAbove)) :=
  AlgebraicTopology.DeRham.Comparison.SmoothCech.cechDelta_apply (ManifoldSheaf.manifoldFormPresheaf E M p) U n c a

/-- The Čech differential evaluates to the signed deletion formula at every
point of its intersection domain. -/
theorem manifoldCechDelta_apply (U : ι → Opens M) (p n : ℕ)
    (c : ManifoldCechCochain (E := E) U p n) (a : Fin (n + 2) → ι)
    (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) :
    manifoldCechDelta U p n c a x =
      CechContractionAlgebra.tupleCoboundary (fun b => (c b).extension (x : M)) a := by
  change openFormEvaluation x (manifoldCechDelta U p n c a) = _
  rw [manifoldCechDelta_sections, map_sum]
  simp only [CechContractionAlgebra.tupleCoboundary]
  apply Finset.sum_congr rfl
  intro j _
  change (-1 : ℤ) ^ j.val •
    c (a ∘ j.succAbove) ⟨x, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a j.succAbove x.property⟩ = _
  exact congrArg (fun value => (-1 : ℤ) ^ j.val • value)
    (Open.SmoothOpenManifoldForm.extension_apply (c (a ∘ j.succAbove))
      ⟨x, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a j.succAbove x.property⟩).symm

section Partition

variable [IsManifold 𝓘(ℝ, E) ∞ M] [Fintype ι]
  (U : ι → Opens M) (rho : ι → M → ℂ)
  (hrho : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (rho i))
  (hsupp : ∀ i, tsupport (rho i) ⊆ (U i : Set M))

/-- The actual partition-of-unity Čech operator. Each summand is a smooth
relative extension from the intersection with the inserted cover member. -/
def manifoldCechContraction (p n : ℕ) :
    ManifoldCechCochain (E := E) U p (n + 1) →ₗ[ℂ]
      ManifoldCechCochain (E := E) U p n where
  toFun c a := ∑ i, Open.SmoothOpenManifoldForm.supportedExtensionTo
    (U i) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (rho i) (hrho i).contMDiffOn (hsupp i)
    (Open.SmoothOpenManifoldForm.restrict (le_of_eq (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_cons U i a).symm)
      (c (Fin.cons i a)))
  map_add' c d := by
    funext a
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' z c := by
    funext a
    simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

/-- Evaluation of the smooth extension operator is weighted insertion of
the actual cochain values, using the canonical auxiliary zero extensions. -/
theorem manifoldCechContraction_apply (p n : ℕ)
    (c : ManifoldCechCochain (E := E) U p (n + 1))
    (a : Fin (n + 1) → ι) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) :
    manifoldCechContraction U rho hrho hsupp p n c a x =
      CechContractionAlgebra.weightedInsertion (fun i => rho i (x : M))
        (fun b => (c b).extension (x : M)) a := by
  change openFormEvaluation x (∑ i,
    Open.SmoothOpenManifoldForm.supportedExtensionTo (U i) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)
      (rho i) (hrho i).contMDiffOn (hsupp i)
      (Open.SmoothOpenManifoldForm.restrict (le_of_eq (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_cons U i a).symm)
        (c (Fin.cons i a)))) = _
  rw [map_sum]
  unfold CechContractionAlgebra.weightedInsertion
  apply Finset.sum_congr rfl
  intro i _
  change Open.SmoothOpenManifoldForm.supportedExtensionTo (U i) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)
    (rho i) (hrho i).contMDiffOn (hsupp i)
    (Open.SmoothOpenManifoldForm.restrict (le_of_eq (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_cons U i a).symm)
      (c (Fin.cons i a))) x = rho i (x : M) • (c (Fin.cons i a)).extension (x : M)
  by_cases hx : (x : M) ∈ U i
  · have hcons : (x : M) ∈ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (Fin.cons i a) := by
      rw [AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_cons]
      exact ⟨hx, x.property⟩
    rw [Open.SmoothOpenManifoldForm.supportedExtensionTo_apply_mem _ _ _ _ _ _ x hx]
    exact congrArg (fun value => rho i (x : M) • value)
      (Open.SmoothOpenManifoldForm.extension_apply (c (Fin.cons i a)) ⟨x, hcons⟩).symm
  · have hzero : rho i (x : M) = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (hsupp i h))
    rw [Open.SmoothOpenManifoldForm.supportedExtensionTo_apply, hzero]
    apply ContinuousAlternatingMap.ext
    intro v
    change (0 : ℂ) * _ = 0 * _
    simp only [zero_mul]

/-- On an intersection domain, differentiating the contraction is the
algebraic deletion operator applied after weighted insertion. -/
theorem manifoldCechDelta_contraction_apply (p n : ℕ)
    (c : ManifoldCechCochain (E := E) U p (n + 1))
    (a : Fin (n + 2) → ι) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) :
    manifoldCechDelta U p n (manifoldCechContraction U rho hrho hsupp p n c) a x =
      CechContractionAlgebra.tupleCoboundary
        (CechContractionAlgebra.weightedInsertion (fun i => rho i (x : M))
          (fun b => (c b).extension (x : M))) a := by
  rw [manifoldCechDelta_apply]
  unfold CechContractionAlgebra.tupleCoboundary
  apply Finset.sum_congr rfl
  intro j _
  have hx : (x : M) ∈ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (a ∘ j.succAbove) :=
    AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a j.succAbove x.property
  apply congrArg (fun value => (-1 : ℤ) ^ j.val • value)
  exact (Open.SmoothOpenManifoldForm.extension_apply
    (manifoldCechContraction U rho hrho hsupp p n c (a ∘ j.succAbove)) ⟨x, hx⟩).trans
    (manifoldCechContraction_apply U rho hrho hsupp p n c (a ∘ j.succAbove) ⟨x, hx⟩)

/-- The support condition permits the differential to be evaluated on every
nonzero weighted summand of the contraction. -/
theorem manifoldCechContraction_delta_apply (p n : ℕ)
    (c : ManifoldCechCochain (E := E) U p (n + 1))
    (a : Fin (n + 2) → ι) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) :
    manifoldCechContraction U rho hrho hsupp p (n + 1)
      (manifoldCechDelta U p (n + 1) c) a x =
      CechContractionAlgebra.weightedInsertion (fun i => rho i (x : M))
        (CechContractionAlgebra.tupleCoboundary (fun b => (c b).extension (x : M))) a := by
  rw [manifoldCechContraction_apply]
  unfold CechContractionAlgebra.weightedInsertion
  apply Finset.sum_congr rfl
  intro i _
  change rho i (x : M) •
    (manifoldCechDelta U p (n + 1) c (Fin.cons i a)).extension (x : M) =
      rho i (x : M) • CechContractionAlgebra.tupleCoboundary (fun b => (c b).extension (x : M)) (Fin.cons i a)
  by_cases hzero : rho i (x : M) = 0
  · rw [hzero]
    apply ContinuousAlternatingMap.ext
    intro v
    change (0 : ℂ) * _ = 0 * _
    simp only [zero_mul]
  · have hx : (x : M) ∈ U i := hsupp i (subset_closure hzero)
    have hcons : (x : M) ∈ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (Fin.cons i a) := by
      rw [AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_cons]
      exact ⟨hx, x.property⟩
    rw [Open.SmoothOpenManifoldForm.extension_apply
      (manifoldCechDelta U p (n + 1) c (Fin.cons i a)) ⟨x, hcons⟩,
      manifoldCechDelta_apply]

/-- The finite partition gives the actual positive-degree Čech homotopy
identity `δ H + H δ = id`. -/
theorem manifoldCech_contraction_identity
    (hsum : ∀ x, ∑ i, rho i x = 1) (p n : ℕ)
    (c : ManifoldCechCochain (E := E) U p (n + 1)) :
    manifoldCechDelta U p n (manifoldCechContraction U rho hrho hsupp p n c) +
      manifoldCechContraction U rho hrho hsupp p (n + 1)
        (manifoldCechDelta U p (n + 1) c) = c := by
  funext a
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  change manifoldCechDelta U p n (manifoldCechContraction U rho hrho hsupp p n c) a x +
    manifoldCechContraction U rho hrho hsupp p (n + 1)
      (manifoldCechDelta U p (n + 1) c) a x = c a x
  rw [manifoldCechDelta_contraction_apply, manifoldCechContraction_delta_apply,
    CechContractionAlgebra.tupleCoboundary_weightedInsertion, hsum, one_smul,
    Open.SmoothOpenManifoldForm.extension_apply]

/-- The same positive-degree homotopy identity as an equality of linear maps. -/
theorem manifoldCech_contraction_linear_identity
    (hsum : ∀ x, ∑ i, rho i x = 1) (p n : ℕ) :
    (manifoldCechDelta U p n).comp (manifoldCechContraction U rho hrho hsupp p n) +
      (manifoldCechContraction U rho hrho hsupp p (n + 1)).comp
        (manifoldCechDelta U p (n + 1)) = LinearMap.id := by
  apply LinearMap.ext
  intro c
  exact manifoldCech_contraction_identity U rho hrho hsupp hsum p n c

/-- In every positive Čech degree, a closed cochain has an explicit primitive. -/
theorem manifoldCech_closed_eq_delta
    (hsum : ∀ x, ∑ i, rho i x = 1) (p n : ℕ)
    (c : ManifoldCechCochain (E := E) U p (n + 1))
    (hc : manifoldCechDelta U p (n + 1) c = 0) :
    manifoldCechDelta U p n (manifoldCechContraction U rho hrho hsupp p n c) = c := by
  have h := manifoldCech_contraction_identity U rho hrho hsupp hsum p n c
  rw [hc, map_zero, add_zero] at h
  exact h

end Partition

/-- A finite open cover of a finite-dimensional Hausdorff sigma-compact
smooth manifold admits an actual linear Čech contraction in all positive
degrees. The partition of unity is constructed by the proved existence
theorem, rather than supplied as an acyclicity hypothesis. -/
theorem exists_manifoldCech_contraction
    [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
    [T2Space M] [SigmaCompactSpace M] [Fintype ι]
    (U : ι → Opens M) (hcover : ∀ x, ∃ i, x ∈ U i) (p : ℕ) :
    ∃ H : ∀ n : ℕ, ManifoldCechCochain (E := E) U p (n + 1) →ₗ[ℂ]
        ManifoldCechCochain (E := E) U p n,
      ∀ n, (manifoldCechDelta U p n).comp (H n) +
        (H (n + 1)).comp (manifoldCechDelta U p (n + 1)) = LinearMap.id := by
  obtain ⟨rho, hrho, hsupp, hsum⟩ := FinitePartition.exists_finite_complex_partition
    (E := E) (fun i => (U i : Set M)) (fun i => (U i).isOpen) hcover
  exact ⟨manifoldCechContraction U rho hrho hsupp p,
    manifoldCech_contraction_linear_identity U rho hrho hsupp hsum p⟩

/-- Every closed positive-degree cochain of this genuine manifold-form
sheaf on a finite open cover is a coboundary. -/
theorem manifoldCech_positive_exact
    [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
    [T2Space M] [SigmaCompactSpace M] [Fintype ι]
    (U : ι → Opens M) (hcover : ∀ x, ∃ i, x ∈ U i) (p n : ℕ)
    (c : ManifoldCechCochain (E := E) U p (n + 1))
    (hc : manifoldCechDelta U p (n + 1) c = 0) :
    ∃ b : ManifoldCechCochain (E := E) U p n, manifoldCechDelta U p n b = c := by
  obtain ⟨H, hH⟩ := exists_manifoldCech_contraction (E := E) U hcover p
  refine ⟨H n c, ?_⟩
  have h := LinearMap.congr_fun (hH n) c
  change manifoldCechDelta U p n (H n c) + H (n + 1)
    (manifoldCechDelta U p (n + 1) c) = c at h
  rw [hc, map_zero, add_zero] at h
  exact h

end

end OAI.Analysis.DifferentialForms.Manifold.CechContraction
