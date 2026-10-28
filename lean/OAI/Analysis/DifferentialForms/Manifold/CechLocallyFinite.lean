import OAI.Analysis.DifferentialForms.Manifold.CechContraction
import OAI.Analysis.DifferentialForms.Manifold.CechLocallyFiniteAlgebra
import OAI.Analysis.DifferentialForms.Manifold.ManifoldLocallyFiniteSum
import OAI.Analysis.DifferentialForms.Manifold.FinitePartition
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Cech Locally Finite -/

namespace OAI.Analysis.DifferentialForms.Manifold.CechLocallyFinite

noncomputable section

/-!
# Actual Čech contraction for arbitrary manifold open covers

The homotopy sums the genuine supported insertion maps. Local finiteness of
the scalar supports makes this a smooth section on each intersection. The
pointwise finite-support tuple identity proves positive-degree exactness.
-/

open _root_.CategoryTheory Function Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff BigOperators

universe u

variable {E M ι : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (U : ι → Opens M) (rho : ι → M → ℂ)
  (hrho : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (rho i))
  (hsupp : ∀ i, tsupport (rho i) ⊆ (U i : Set M))

/-- One actual supported insertion map, before summing over cover indices. -/
def manifoldCechWeightedInsertion (p n : ℕ) (i : ι) :
    CechContraction.ManifoldCechCochain (E := E) U p (n + 1) →ₗ[ℂ]
      CechContraction.ManifoldCechCochain (E := E) U p n where
  toFun c a := Open.SmoothOpenManifoldForm.supportedExtensionTo
    (U i) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (rho i) (hrho i).contMDiffOn (hsupp i)
    (Open.SmoothOpenManifoldForm.restrict (le_of_eq (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_cons U i a).symm)
      (c (Fin.cons i a)))
  map_add' c d := by
    funext a
    simp only [Pi.add_apply, map_add]
  map_smul' z c := by
    funext a
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply]

theorem manifoldCechWeightedInsertion_apply (p n : ℕ) (i : ι)
    (c : CechContraction.ManifoldCechCochain (E := E) U p (n + 1))
    (a : Fin (n + 1) → ι) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) :
    manifoldCechWeightedInsertion U rho hrho hsupp p n i c a x =
      rho i (x : M) • (c (Fin.cons i a)).extension (x : M) := by
  change Open.SmoothOpenManifoldForm.supportedExtensionTo (U i) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)
    (rho i) (hrho i).contMDiffOn (hsupp i)
    (Open.SmoothOpenManifoldForm.restrict (le_of_eq (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_cons U i a).symm)
      (c (Fin.cons i a))) x = _
  by_cases hx : (x : M) ∈ U i
  · have hcons : (x : M) ∈ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (Fin.cons i a) := by
      rw [AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_cons]
      exact ⟨hx, x.property⟩
    rw [Open.SmoothOpenManifoldForm.supportedExtensionTo_apply_mem _ _ _ _ _ _ x hx]
    exact congrArg (fun value => rho i (x : M) • value)
      (Open.SmoothOpenManifoldForm.extension_apply (c (Fin.cons i a)) ⟨x, hcons⟩).symm
  · have hz : rho i (x : M) = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (hsupp i h))
    rw [Open.SmoothOpenManifoldForm.supportedExtensionTo_apply, hz]
    apply ContinuousAlternatingMap.ext
    intro v
    change (0 : ℂ) * _ = 0 * _
    simp only [zero_mul]

variable (hlf : LocallyFinite (fun i => support (rho i)))

include hlf in
theorem manifoldCechWeightedInsertion_locallyFinite (p n : ℕ)
    (c : CechContraction.ManifoldCechCochain (E := E) U p (n + 1)) (a : Fin (n + 1) → ι) :
    LocallyFinite (fun i => {x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a |
      manifoldCechWeightedInsertion U rho hrho hsupp p n i c a x ≠ 0}) := by
  apply (hlf.preimage_continuous continuous_subtype_val).subset
  intro i x hx hz
  apply hx
  rw [manifoldCechWeightedInsertion_apply]
  change rho i (x : M) = 0 at hz
  rw [hz]
  exact zero_smul ℂ ((c (Fin.cons i a)).extension (x : M))

/-- The supported insertion sum is a genuine complex-linear map on the
manifold-form Čech cochains for an arbitrary index set. -/
def manifoldCechLocallyFiniteContraction (p n : ℕ) :
    CechContraction.ManifoldCechCochain (E := E) U p (n + 1) →ₗ[ℂ]
      CechContraction.ManifoldCechCochain (E := E) U p n where
  toFun c a := Open.SmoothOpenManifoldForm.locallyFiniteSum
    (fun i => manifoldCechWeightedInsertion U rho hrho hsupp p n i c a)
    (manifoldCechWeightedInsertion_locallyFinite U rho hrho hsupp hlf p n c a)
  map_add' c d := by
    funext a
    apply Open.SmoothOpenManifoldForm.ext
    intro x
    change (∑ᶠ i, manifoldCechWeightedInsertion U rho hrho hsupp p n i (c + d) a x) =
      (∑ᶠ i, manifoldCechWeightedInsertion U rho hrho hsupp p n i c a x) +
      (∑ᶠ i, manifoldCechWeightedInsertion U rho hrho hsupp p n i d a x)
    have hterm (i : ι) :
        manifoldCechWeightedInsertion U rho hrho hsupp p n i (c + d) a x =
          manifoldCechWeightedInsertion U rho hrho hsupp p n i c a x +
            manifoldCechWeightedInsertion U rho hrho hsupp p n i d a x :=
      congrArg (fun z : CechContraction.ManifoldCechCochain (E := E) U p n => z a x)
        ((manifoldCechWeightedInsertion U rho hrho hsupp p n i).map_add c d)
    exact (finsum_congr hterm).trans (finsum_add_distrib
      ((manifoldCechWeightedInsertion_locallyFinite U rho hrho hsupp hlf p n c a).point_finite x)
      ((manifoldCechWeightedInsertion_locallyFinite U rho hrho hsupp hlf p n d a).point_finite x))
  map_smul' z c := by
    funext a
    apply Open.SmoothOpenManifoldForm.ext
    intro x
    change (∑ᶠ i, manifoldCechWeightedInsertion U rho hrho hsupp p n i (z • c) a x) =
      z • (∑ᶠ i, manifoldCechWeightedInsertion U rho hrho hsupp p n i c a x)
    have hterm (i : ι) :
        manifoldCechWeightedInsertion U rho hrho hsupp p n i (z • c) a x =
          z • manifoldCechWeightedInsertion U rho hrho hsupp p n i c a x :=
      congrArg (fun w : CechContraction.ManifoldCechCochain (E := E) U p n => w a x)
        ((manifoldCechWeightedInsertion U rho hrho hsupp p n i).map_smul z c)
    exact (finsum_congr hterm).trans (smul_finsum' z
      ((manifoldCechWeightedInsertion_locallyFinite U rho hrho hsupp hlf p n c a).point_finite x)).symm

theorem manifoldCechLocallyFiniteContraction_apply (p n : ℕ)
    (c : CechContraction.ManifoldCechCochain (E := E) U p (n + 1))
    (a : Fin (n + 1) → ι) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) :
    manifoldCechLocallyFiniteContraction U rho hrho hsupp hlf p n c a x =
      CechLocallyFiniteAlgebra.finsumWeightedInsertion (fun i => rho i (x : M))
        (fun b => (c b).extension (x : M)) a := by
  change (∑ᶠ i, manifoldCechWeightedInsertion U rho hrho hsupp p n i c a x) = _
  exact finsum_congr fun i => manifoldCechWeightedInsertion_apply U rho hrho hsupp p n i c a x

theorem manifoldCechDelta_locallyFiniteContraction_apply (p n : ℕ)
    (c : CechContraction.ManifoldCechCochain (E := E) U p (n + 1))
    (a : Fin (n + 2) → ι) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) :
    CechContraction.manifoldCechDelta U p n (manifoldCechLocallyFiniteContraction U rho hrho hsupp hlf p n c) a x =
      CechContractionAlgebra.tupleCoboundary
        (CechLocallyFiniteAlgebra.finsumWeightedInsertion (fun i => rho i (x : M))
          (fun b => (c b).extension (x : M))) a := by
  rw [CechContraction.manifoldCechDelta_apply]
  unfold CechContractionAlgebra.tupleCoboundary
  apply Finset.sum_congr rfl
  intro j _
  have hx : (x : M) ∈ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (a ∘ j.succAbove) :=
    AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a j.succAbove x.property
  apply congrArg (fun value => (-1 : ℤ) ^ j.val • value)
  exact (Open.SmoothOpenManifoldForm.extension_apply
    (manifoldCechLocallyFiniteContraction U rho hrho hsupp hlf p n c (a ∘ j.succAbove))
      ⟨x, hx⟩).trans
    (manifoldCechLocallyFiniteContraction_apply U rho hrho hsupp hlf p n c
      (a ∘ j.succAbove) ⟨x, hx⟩)

theorem manifoldCechLocallyFiniteContraction_delta_apply (p n : ℕ)
    (c : CechContraction.ManifoldCechCochain (E := E) U p (n + 1))
    (a : Fin (n + 2) → ι) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) :
    manifoldCechLocallyFiniteContraction U rho hrho hsupp hlf p (n + 1)
      (CechContraction.manifoldCechDelta U p (n + 1) c) a x =
      CechLocallyFiniteAlgebra.finsumWeightedInsertion (fun i => rho i (x : M))
        (CechContractionAlgebra.tupleCoboundary (fun b => (c b).extension (x : M))) a := by
  rw [manifoldCechLocallyFiniteContraction_apply]
  unfold CechLocallyFiniteAlgebra.finsumWeightedInsertion
  apply finsum_congr
  intro i
  change rho i (x : M) • (CechContraction.manifoldCechDelta U p (n + 1) c (Fin.cons i a)).extension
      (x : M) = rho i (x : M) •
        CechContractionAlgebra.tupleCoboundary (fun b => (c b).extension (x : M)) (Fin.cons i a)
  by_cases hz : rho i (x : M) = 0
  · rw [hz]
    apply ContinuousAlternatingMap.ext
    intro v
    change (0 : ℂ) * _ = 0 * _
    simp only [zero_mul]
  · have hx : (x : M) ∈ U i := hsupp i (subset_closure hz)
    have hcons : (x : M) ∈ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (Fin.cons i a) := by
      rw [AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_cons]
      exact ⟨hx, x.property⟩
    rw [Open.SmoothOpenManifoldForm.extension_apply
      (CechContraction.manifoldCechDelta U p (n + 1) c (Fin.cons i a)) ⟨x, hcons⟩,
      CechContraction.manifoldCechDelta_apply]

/-- The actual arbitrary-index positive-degree homotopy identity. -/
theorem manifoldCech_locallyFinite_contraction_identity
    (hsum : ∀ x, ∑ᶠ i, rho i x = 1) (p n : ℕ)
    (c : CechContraction.ManifoldCechCochain (E := E) U p (n + 1)) :
    CechContraction.manifoldCechDelta U p n (manifoldCechLocallyFiniteContraction U rho hrho hsupp hlf p n c) +
      manifoldCechLocallyFiniteContraction U rho hrho hsupp hlf p (n + 1)
        (CechContraction.manifoldCechDelta U p (n + 1) c) = c := by
  funext a
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  change CechContraction.manifoldCechDelta U p n
      (manifoldCechLocallyFiniteContraction U rho hrho hsupp hlf p n c) a x +
    manifoldCechLocallyFiniteContraction U rho hrho hsupp hlf p (n + 1)
      (CechContraction.manifoldCechDelta U p (n + 1) c) a x = c a x
  rw [manifoldCechDelta_locallyFiniteContraction_apply,
    manifoldCechLocallyFiniteContraction_delta_apply,
    CechLocallyFiniteAlgebra.tupleCoboundary_finsumWeightedInsertion _ (hlf.point_finite (x : M)),
    hsum, one_smul, Open.SmoothOpenManifoldForm.extension_apply]

theorem manifoldCech_locallyFinite_contraction_linear_identity
    (hsum : ∀ x, ∑ᶠ i, rho i x = 1) (p n : ℕ) :
    (CechContraction.manifoldCechDelta U p n).comp (manifoldCechLocallyFiniteContraction U rho hrho hsupp hlf p n) +
      (manifoldCechLocallyFiniteContraction U rho hrho hsupp hlf p (n + 1)).comp
        (CechContraction.manifoldCechDelta U p (n + 1)) = LinearMap.id := by
  apply LinearMap.ext
  intro c
  exact manifoldCech_locallyFinite_contraction_identity U rho hrho hsupp hlf hsum p n c

/-- Every closed positive-degree cochain has the constructed primitive. -/
theorem manifoldCech_locallyFinite_closed_eq_delta
    (hsum : ∀ x, ∑ᶠ i, rho i x = 1) (p n : ℕ)
    (c : CechContraction.ManifoldCechCochain (E := E) U p (n + 1))
    (hc : CechContraction.manifoldCechDelta U p (n + 1) c = 0) :
    CechContraction.manifoldCechDelta U p n (manifoldCechLocallyFiniteContraction U rho hrho hsupp hlf p n c) = c := by
  have h := manifoldCech_locallyFinite_contraction_identity U rho hrho hsupp hlf hsum p n c
  rw [hc, map_zero, add_zero] at h
  exact h

include rho hrho hsupp hlf in
theorem manifoldCech_locallyFinite_range_eq_ker
    (hsum : ∀ x, ∑ᶠ i, rho i x = 1) (p n : ℕ) :
    LinearMap.range (CechContraction.manifoldCechDelta (E := E) U p n) =
      LinearMap.ker (CechContraction.manifoldCechDelta (E := E) U p (n + 1)) := by
  apply le_antisymm
  · rintro c ⟨b, rfl⟩
    exact CechContraction.manifoldCechDelta_squared U p n b
  · intro c hc
    exact ⟨manifoldCechLocallyFiniteContraction U rho hrho hsupp hlf p n c,
      manifoldCech_locallyFinite_closed_eq_delta U rho hrho hsupp hlf hsum p n c hc⟩

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]

/-- Construct the actual positive-degree homotopy for any open cover using
mathlib's smooth locally finite partition of unity. -/
theorem exists_manifoldCech_locallyFinite_contraction
    (hcover : ∀ x, ∃ i, x ∈ U i) (p : ℕ) :
    ∃ H : ∀ n : ℕ, CechContraction.ManifoldCechCochain (E := E) U p (n + 1) →ₗ[ℂ]
        CechContraction.ManifoldCechCochain (E := E) U p n,
      ∀ n, (CechContraction.manifoldCechDelta U p n).comp (H n) +
        (H (n + 1)).comp (CechContraction.manifoldCechDelta U p (n + 1)) = LinearMap.id := by
  obtain ⟨rho, hrho, hlf, hsupp, hsum⟩ := FinitePartition.exists_locallyFinite_complex_partition
    (E := E) (fun i => (U i : Set M)) (fun i => (U i).isOpen) hcover
  exact ⟨manifoldCechLocallyFiniteContraction U rho hrho hsupp hlf p,
    manifoldCech_locallyFinite_contraction_linear_identity U rho hrho hsupp hlf hsum p⟩

theorem manifoldCech_positive_exact_of_arbitrary_cover
    (hcover : ∀ x, ∃ i, x ∈ U i) (p n : ℕ)
    (c : CechContraction.ManifoldCechCochain (E := E) U p (n + 1))
    (hc : CechContraction.manifoldCechDelta U p (n + 1) c = 0) :
    ∃ b : CechContraction.ManifoldCechCochain (E := E) U p n, CechContraction.manifoldCechDelta U p n b = c := by
  obtain ⟨H, hH⟩ := exists_manifoldCech_locallyFinite_contraction (E := E) U hcover p
  refine ⟨H n c, ?_⟩
  have h := LinearMap.congr_fun (hH n) c
  change CechContraction.manifoldCechDelta U p n (H n c) + H (n + 1)
    (CechContraction.manifoldCechDelta U p (n + 1) c) = c at h
  rw [hc, map_zero, add_zero] at h
  exact h

theorem manifoldCechDelta_range_eq_ker_of_arbitrary_cover
    (hcover : ∀ x, ∃ i, x ∈ U i) (p n : ℕ) :
    LinearMap.range (CechContraction.manifoldCechDelta (E := E) U p n) =
      LinearMap.ker (CechContraction.manifoldCechDelta (E := E) U p (n + 1)) := by
  apply le_antisymm
  · rintro c ⟨b, rfl⟩
    exact CechContraction.manifoldCechDelta_squared U p n b
  · intro c hc
    exact manifoldCech_positive_exact_of_arbitrary_cover U hcover p n c hc

theorem manifoldCech_functionExact_of_arbitrary_cover
    (hcover : ∀ x, ∃ i, x ∈ U i) (p n : ℕ) :
    Function.Exact (CechContraction.manifoldCechDelta (E := E) U p n)
      (CechContraction.manifoldCechDelta (E := E) U p (n + 1)) := by
  intro c
  constructor
  · exact manifoldCech_positive_exact_of_arbitrary_cover U hcover p n c
  · rintro ⟨b, rfl⟩
    exact CechContraction.manifoldCechDelta_squared U p n b

/-- Positive rows are exact in the categorical interface used by total-complex
comparison, with no finite-index assumption on the cover. -/
theorem manifoldCech_exactAt_succ_of_arbitrary_cover
    (hcover : ∀ x, ∃ i, x ∈ U i) (p n : ℕ) :
    (CechContraction.manifoldCechComplex (E := E) U p).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  change Function.Exact
    ((CechContraction.manifoldCechComplex (E := E) U p).d n (n + 1))
    ((CechContraction.manifoldCechComplex (E := E) U p).d (n + 1) (n + 2))
  rw [CechContraction.manifoldCechComplex_d, CechContraction.manifoldCechComplex_d]
  exact manifoldCech_functionExact_of_arbitrary_cover U hcover p n

end

end OAI.Analysis.DifferentialForms.Manifold.CechLocallyFinite
