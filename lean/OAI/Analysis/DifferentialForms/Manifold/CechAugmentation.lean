import OAI.Analysis.DifferentialForms.Manifold.CechContraction
import OAI.Analysis.DifferentialForms.Manifold.PartitionPatch
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.QuasiIso

/-! # Cech Augmentation -/

namespace OAI.Analysis.DifferentialForms.Manifold.CechAugmentation

noncomputable section

/-!
The actual global augmentation of manifold-form Čech cochains. Genuine
smooth-section gluing proves degree-zero exactness on any open cover.
For finite covers this combines with the constructed partition contraction
to give exact augmented rows in all degrees.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff BigOperators

universe u

variable {E M ι : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  (U : ι → Opens M) (p : ℕ)

/-- A singleton Čech intersection is the indicated cover member. -/
theorem manifoldCechIntersection_singleton (a : Fin 1 → ι) :
    AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a = U (a 0) := by
  apply le_antisymm
  · exact AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0
  · apply le_iInf
    intro k
    have hk : k = 0 := Fin.eq_zero k
    subst k
    exact le_refl _

/-- Read degree-zero cochains as the actual family of cover sections. -/
def manifoldCechZeroFamily : CechContraction.ManifoldCechCochain (E := E) U p 0 →ₗ[ℂ]
    ((i : ι) → Open.SmoothOpenManifoldForm E (U i) p) where
  toFun c i := Open.SmoothOpenManifoldForm.restrict
    (le_of_eq (manifoldCechIntersection_singleton U (fun _ => i)).symm) (c (fun _ => i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The local-section family retains the complete degree-zero cochain. -/
theorem manifoldCechZeroFamily_restrict (c : CechContraction.ManifoldCechCochain (E := E) U p 0)
    (a : Fin 1 → ι) :
    Open.SmoothOpenManifoldForm.restrict (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0)
      (manifoldCechZeroFamily U p c (a 0)) = c a := by
  obtain ⟨i, rfl⟩ : ∃ i : ι, a = (fun _ : Fin 1 => i) :=
    ⟨a 0, funext (fun k => congrArg a (Fin.eq_zero k))⟩
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  rfl

theorem manifoldCechZeroFamily_injective :
    Function.Injective (manifoldCechZeroFamily (E := E) U p) := by
  intro c d h
  funext a
  rw [← manifoldCechZeroFamily_restrict U p c a,
    ← manifoldCechZeroFamily_restrict U p d a, h]

/-- The first Čech differential is the difference of restrictions on an overlap. -/
theorem manifoldCechDelta_zero_apply (c : CechContraction.ManifoldCechCochain (E := E) U p 0)
    (a : Fin 2 → ι) :
    CechContraction.manifoldCechDelta U p 0 c a =
      Open.SmoothOpenManifoldForm.restrict (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1)
        (manifoldCechZeroFamily U p c (a 1)) -
      Open.SmoothOpenManifoldForm.restrict (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0)
        (manifoldCechZeroFamily U p c (a 0)) := by
  rw [CechContraction.manifoldCechDelta_sections]
  change (∑ j : Fin 2, (-1 : ℤ) ^ j.val •
    Open.SmoothOpenManifoldForm.restrict (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a j.succAbove)
      (c (a ∘ j.succAbove))) = _
  simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, Fin.val_one, pow_one]
  rw [← manifoldCechZeroFamily_restrict U p c (a ∘ (0 : Fin 2).succAbove),
    ← manifoldCechZeroFamily_restrict U p c (a ∘ (1 : Fin 2).succAbove)]
  rw [Open.SmoothOpenManifoldForm.restrict_trans, Open.SmoothOpenManifoldForm.restrict_trans]
  let s : Open.SmoothOpenManifoldForm E (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) p :=
    Open.SmoothOpenManifoldForm.restrict (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1)
      (manifoldCechZeroFamily U p c (a 1))
  let t : Open.SmoothOpenManifoldForm E (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) p :=
    Open.SmoothOpenManifoldForm.restrict (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0)
      (manifoldCechZeroFamily U p c (a 0))
  change (1 : ℤ) • s + (-1 : ℤ) • t = s - t
  exact (congrArg₂ (fun x y : Open.SmoothOpenManifoldForm E (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) p => x + y)
    (one_smul ℤ s) (neg_one_smul ℤ t)).trans (sub_eq_add_neg s t).symm

/-- Closed degree-zero cochains are precisely compatible actual local forms. -/
theorem manifoldCechDelta_zero_iff_compatible
    (c : CechContraction.ManifoldCechCochain (E := E) U p 0) :
    CechContraction.manifoldCechDelta U p 0 c = 0 ↔
      Open.SmoothOpenManifoldForm.Compatible (manifoldCechZeroFamily U p c) := by
  constructor
  · intro hc i j x hi hj
    let a : Fin 2 → ι := ![i, j]
    have hx : x ∈ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a := by
      apply (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection U a x).2
      exact Fin.forall_fin_two.2 ⟨hi, hj⟩
    have heq := congrFun hc a
    rw [manifoldCechDelta_zero_apply] at heq
    have heqpoint := congrArg
      (fun f : Open.SmoothOpenManifoldForm E (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) p => f ⟨x, hx⟩) heq
    change manifoldCechZeroFamily U p c j ⟨x, hj⟩ -
      manifoldCechZeroFamily U p c i ⟨x, hi⟩ = 0 at heqpoint
    exact (sub_eq_zero.mp heqpoint).symm
  · intro hc
    funext a
    rw [manifoldCechDelta_zero_apply]
    apply Open.SmoothOpenManifoldForm.ext
    intro x
    exact sub_eq_zero.mpr (hc (a 1) (a 0) x (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property))

/-- The augmentation is the actual restriction of a global smooth manifold form. -/
def manifoldCechAugmentation : Manifold.Algebra.SmoothManifoldForm E M p →ₗ[ℂ]
    CechContraction.ManifoldCechCochain (E := E) U p 0 :=
  LinearMap.pi (fun a => Manifold.Algebra.SmoothManifoldForm.onOpen (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))

@[simp]
theorem manifoldCechAugmentation_apply (form : Manifold.Algebra.SmoothManifoldForm E M p)
    (a : Fin 1 → ι) :
    manifoldCechAugmentation U p form a =
      Manifold.Algebra.SmoothManifoldForm.onOpen (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) form := rfl

theorem manifoldCechZeroFamily_augmentation (form : Manifold.Algebra.SmoothManifoldForm E M p) (i : ι) :
    manifoldCechZeroFamily U p (manifoldCechAugmentation U p form) i =
      Manifold.Algebra.SmoothManifoldForm.onOpen (U i) form := by
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  rfl

/-- A restricted global form is a genuine Čech zero cocycle. -/
theorem manifoldCechDelta_augmentation (form : Manifold.Algebra.SmoothManifoldForm E M p) :
    CechContraction.manifoldCechDelta U p 0 (manifoldCechAugmentation U p form) = 0 := by
  apply (manifoldCechDelta_zero_iff_compatible U p _).2
  intro i j x hi hj
  rw [manifoldCechZeroFamily_augmentation, manifoldCechZeroFamily_augmentation]
  rfl

/-- The augmentation is natural for the exterior derivative. -/
theorem manifoldCechAugmentation_d [IsManifold 𝓘(ℝ, E) ∞ M]
    (form : Manifold.Algebra.SmoothManifoldForm E M p) (a : Fin 1 → ι) :
    Open.SmoothOpenManifoldForm.d (manifoldCechAugmentation U p form a) =
      manifoldCechAugmentation U (p + 1) (Manifold.Algebra.SmoothManifoldForm.d form) a :=
  Manifold.Algebra.SmoothManifoldForm.onOpen_d (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) form

/-- The global restriction map with codomain restricted to zero cocycles. -/
def manifoldCechAugmentationToCycles : Manifold.Algebra.SmoothManifoldForm E M p →ₗ[ℂ]
    LinearMap.ker (CechContraction.manifoldCechDelta (E := E) U p 0) :=
  (manifoldCechAugmentation U p).codRestrict _
    (fun form => manifoldCechDelta_augmentation U p form)

variable (hcover : ∀ x : M, ∃ i, x ∈ U i)

include hcover

/-- Restriction to an actual open cover distinguishes global forms. -/
theorem manifoldCechAugmentation_injective :
    Function.Injective (manifoldCechAugmentation (E := E) U p) := by
  intro form other h
  apply Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  obtain ⟨i, hi⟩ := hcover x
  have hr := congrArg (fun c => manifoldCechZeroFamily U p c i) h
  rw [manifoldCechZeroFamily_augmentation, manifoldCechZeroFamily_augmentation] at hr
  exact congrArg (fun f : Open.SmoothOpenManifoldForm E (U i) p => f ⟨x, hi⟩) hr

/-- Genuine manifold-form gluing produces a global form for every zero cocycle. -/
theorem manifoldCechAugmentationToCycles_surjective :
    Function.Surjective (manifoldCechAugmentationToCycles (E := E) U p) := by
  intro c
  let family := manifoldCechZeroFamily U p c.val
  have hc : Open.SmoothOpenManifoldForm.Compatible family :=
    (manifoldCechDelta_zero_iff_compatible U p c.val).1 c.property
  have hcov : ((⊤ : Opens M) : Set M) ⊆ ⋃ i, (U i : Set M) :=
    fun x _ => Set.mem_iUnion.mpr (hcover x)
  let glued := Open.SmoothOpenManifoldForm.glue (fun _ => le_top) hcov family hc
  refine ⟨Open.SmoothOpenManifoldForm.toGlobal glued, ?_⟩
  apply Subtype.ext
  apply manifoldCechZeroFamily_injective U p
  funext i
  change manifoldCechZeroFamily U p
    (manifoldCechAugmentation U p (Open.SmoothOpenManifoldForm.toGlobal glued)) i = family i
  rw [manifoldCechZeroFamily_augmentation]
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  rw [Manifold.Algebra.SmoothManifoldForm.onOpen_apply, Open.SmoothOpenManifoldForm.toGlobal_apply]
  exact Open.SmoothOpenManifoldForm.glue_apply (fun _ => le_top) hcov family hc
    ⟨x, by simp⟩ i x.property

/-- Global forms are canonically equivalent to Čech zero cocycles on any cover. -/
def manifoldCechGlobalEquivCycles : Manifold.Algebra.SmoothManifoldForm E M p ≃ₗ[ℂ]
    LinearMap.ker (CechContraction.manifoldCechDelta (E := E) U p 0) :=
  LinearEquiv.ofBijective (manifoldCechAugmentationToCycles U p)
    ⟨fun _ _ h => manifoldCechAugmentation_injective U p hcover (congrArg Subtype.val h),
      manifoldCechAugmentationToCycles_surjective U p hcover⟩

@[simp]
theorem manifoldCechGlobalEquivCycles_apply (form : Manifold.Algebra.SmoothManifoldForm E M p) :
    (manifoldCechGlobalEquivCycles U p hcover form).val =
      manifoldCechAugmentation U p form := rfl

/-- Exactness at degree zero, proved by smooth-section gluing. -/
theorem manifoldCechAugmentation_range :
    LinearMap.range (manifoldCechAugmentation (E := E) U p) =
      LinearMap.ker (CechContraction.manifoldCechDelta (E := E) U p 0) := by
  apply le_antisymm
  · rintro c ⟨form, rfl⟩
    exact manifoldCechDelta_augmentation U p form
  · intro c hc
    obtain ⟨form, hform⟩ := manifoldCechAugmentationToCycles_surjective
      U p hcover ⟨c, hc⟩
    exact ⟨form, congrArg Subtype.val hform⟩

/-- The augmented row is exact in the elementwise interface used by total-complex proofs. -/
theorem manifoldCechAugmentation_exact :
    Function.Exact (manifoldCechAugmentation (E := E) U p)
      (CechContraction.manifoldCechDelta (E := E) U p 0) :=
  LinearMap.exact_iff.mpr (manifoldCechAugmentation_range U p hcover).symm

/-- An explicit elementwise form of degree-zero row exactness. -/
theorem manifoldCech_zero_primitive (c : CechContraction.ManifoldCechCochain (E := E) U p 0)
    (hc : CechContraction.manifoldCechDelta U p 0 c = 0) :
    ∃ form : Manifold.Algebra.SmoothManifoldForm E M p, manifoldCechAugmentation U p form = c :=
  (manifoldCechAugmentation_exact U p hcover c).mp hc

omit hcover

section Partition

variable [IsManifold 𝓘(ℝ, E) ∞ M] [Fintype ι]
  (rho : ι → M → ℂ)
  (hrho : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (rho i))
  (hsupp : ∀ i, tsupport (rho i) ⊆ (U i : Set M))

/-- The actual finite partition patch, applied to a degree-zero Čech cochain. -/
def manifoldCechAugmentationPatch : CechContraction.ManifoldCechCochain (E := E) U p 0 →ₗ[ℂ]
    Manifold.Algebra.SmoothManifoldForm E M p :=
  (PartitionPatch.manifoldPartitionPatch U rho hrho hsupp p).comp (manifoldCechZeroFamily U p)

theorem manifoldCechAugmentationPatch_apply (c : CechContraction.ManifoldCechCochain (E := E) U p 0)
    (x : M) :
    manifoldCechAugmentationPatch U p rho hrho hsupp c x =
      ∑ i, rho i x • (manifoldCechZeroFamily U p c i).extension x :=
  PartitionPatch.manifoldPartitionPatch_apply U rho hrho hsupp p (manifoldCechZeroFamily U p c) x

variable (hsum : ∀ x, ∑ i, rho i x = 1)

include hsum

/-- Patching restrictions of a global form recovers the original form. -/
theorem manifoldCechAugmentationPatch_augmentation (form : Manifold.Algebra.SmoothManifoldForm E M p) :
    manifoldCechAugmentationPatch U p rho hrho hsupp
      (manifoldCechAugmentation U p form) = form := by
  change PartitionPatch.manifoldPartitionPatch U rho hrho hsupp p
    (manifoldCechZeroFamily U p (manifoldCechAugmentation U p form)) = form
  have hfamily : manifoldCechZeroFamily U p (manifoldCechAugmentation U p form) =
      PartitionPatch.manifoldCoverRestriction U p form := by
    funext i
    exact manifoldCechZeroFamily_augmentation U p form i
  rw [hfamily]
  exact PartitionPatch.manifoldPartitionPatch_restriction U rho hrho hsupp hsum p form

/-- The partition patch gives the global primitive of a Čech zero cocycle. -/
theorem manifoldCechAugmentation_patch_of_closed
    (c : CechContraction.ManifoldCechCochain (E := E) U p 0) (hc : CechContraction.manifoldCechDelta U p 0 c = 0) :
    manifoldCechAugmentation U p (manifoldCechAugmentationPatch U p rho hrho hsupp c) = c := by
  apply manifoldCechZeroFamily_injective U p
  funext i
  rw [manifoldCechZeroFamily_augmentation]
  exact PartitionPatch.manifoldPartitionPatch_restrict_compatible U rho hrho hsupp hsum p
    (manifoldCechZeroFamily U p c) ((manifoldCechDelta_zero_iff_compatible U p c).mp hc) i

/-- At degree zero, the existing positive contraction leaves exactly the
global partition patch as its correction term. -/
theorem manifoldCechContraction_zero_delta_apply
    (c : CechContraction.ManifoldCechCochain (E := E) U p 0) (a : Fin 1 → ι)
    (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) :
    CechContraction.manifoldCechContraction U rho hrho hsupp p 0 (CechContraction.manifoldCechDelta U p 0 c) a x =
      c a x - manifoldCechAugmentationPatch U p rho hrho hsupp c (x : M) := by
  rw [CechContraction.manifoldCechContraction_apply]
  change (∑ i, rho i (x : M) •
    (CechContraction.manifoldCechDelta U p 0 c (Fin.cons i a)).extension (x : M)) = _
  have hterm (i : ι) : rho i (x : M) •
      (CechContraction.manifoldCechDelta U p 0 c (Fin.cons i a)).extension (x : M) =
      rho i (x : M) • c a x -
        rho i (x : M) • (manifoldCechZeroFamily U p c i).extension (x : M) := by
    by_cases hzero : rho i (x : M) = 0
    · rw [hzero]
      apply ContinuousAlternatingMap.ext
      intro v
      change (0 : ℂ) * _ = 0 * _ - 0 * _
      simp only [zero_mul, sub_zero]
    · have hx : (x : M) ∈ U i := hsupp i (subset_closure hzero)
      have hcons : (x : M) ∈ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (Fin.cons i a) := by
        rw [AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_cons]
        exact ⟨hx, x.property⟩
      have hfirst : manifoldCechZeroFamily U p c (a 0)
          ⟨x, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property⟩ = c a x :=
        congrArg (fun f : Open.SmoothOpenManifoldForm E (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) p => f x)
          (manifoldCechZeroFamily_restrict U p c a)
      have hdelta : (CechContraction.manifoldCechDelta U p 0 c (Fin.cons i a)).extension (x : M) =
          c a x - (manifoldCechZeroFamily U p c i).extension (x : M) := by
        rw [Open.SmoothOpenManifoldForm.extension_apply
          (CechContraction.manifoldCechDelta U p 0 c (Fin.cons i a)) ⟨x, hcons⟩,
          manifoldCechDelta_zero_apply]
        change manifoldCechZeroFamily U p c (a 0)
            ⟨x, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property⟩ -
          manifoldCechZeroFamily U p c i ⟨x, hx⟩ = _
        exact congrArg₂ (fun s t : TangentSpace 𝓘(ℝ, E) (x : M) [⋀^Fin p]→L[ℝ] ℂ => s - t)
          hfirst (Open.SmoothOpenManifoldForm.extension_apply
            (manifoldCechZeroFamily U p c i) ⟨x, hx⟩).symm
      rw [hdelta, smul_sub]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul,
    manifoldCechAugmentationPatch_apply]

/-- The degree-zero augmented homotopy identity on genuine section families. -/
theorem manifoldCech_augmented_contraction_zero
    (c : CechContraction.ManifoldCechCochain (E := E) U p 0) :
    manifoldCechAugmentation U p (manifoldCechAugmentationPatch U p rho hrho hsupp c) +
      CechContraction.manifoldCechContraction U rho hrho hsupp p 0 (CechContraction.manifoldCechDelta U p 0 c) = c := by
  funext a
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  change manifoldCechAugmentationPatch U p rho hrho hsupp c (x : M) +
    CechContraction.manifoldCechContraction U rho hrho hsupp p 0 (CechContraction.manifoldCechDelta U p 0 c) a x = c a x
  rw [manifoldCechContraction_zero_delta_apply U p rho hrho hsupp hsum]
  abel

end Partition

include hcover

variable [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
  [T2Space M] [SigmaCompactSpace M] [Fintype ι]

/-- All the operators of the augmented Čech contraction exist for an actual
finite open cover, including its global term and degree-zero identity. -/
theorem exists_manifoldCech_augmented_contraction :
    ∃ P : CechContraction.ManifoldCechCochain (E := E) U p 0 →ₗ[ℂ] Manifold.Algebra.SmoothManifoldForm E M p,
      ∃ H : ∀ n : ℕ, CechContraction.ManifoldCechCochain (E := E) U p (n + 1) →ₗ[ℂ]
          CechContraction.ManifoldCechCochain (E := E) U p n,
        P.comp (manifoldCechAugmentation U p) = LinearMap.id ∧
        (manifoldCechAugmentation U p).comp P +
          (H 0).comp (CechContraction.manifoldCechDelta U p 0) = LinearMap.id ∧
        ∀ n, (CechContraction.manifoldCechDelta U p n).comp (H n) +
          (H (n + 1)).comp (CechContraction.manifoldCechDelta U p (n + 1)) = LinearMap.id := by
  obtain ⟨rho, hrho, hsupp, hsum⟩ := FinitePartition.exists_finite_complex_partition
    (E := E) (fun i => (U i : Set M)) (fun i => (U i).isOpen) hcover
  refine ⟨manifoldCechAugmentationPatch U p rho hrho hsupp,
    CechContraction.manifoldCechContraction U rho hrho hsupp p, ?_, ?_, ?_⟩
  · apply LinearMap.ext
    intro form
    exact manifoldCechAugmentationPatch_augmentation U p rho hrho hsupp hsum form
  · apply LinearMap.ext
    intro c
    exact manifoldCech_augmented_contraction_zero U p rho hrho hsupp hsum c
  · exact CechContraction.manifoldCech_contraction_linear_identity U rho hrho hsupp hsum p

/-- Positive row exactness in the elementwise interface used by double-complex proofs. -/
theorem manifoldCech_positive_functionExact (n : ℕ) :
    Function.Exact (CechContraction.manifoldCechDelta (E := E) U p n)
      (CechContraction.manifoldCechDelta (E := E) U p (n + 1)) := by
  intro c
  constructor
  · exact CechContraction.manifoldCech_positive_exact U hcover p n c
  · rintro ⟨b, rfl⟩
    exact CechContraction.manifoldCechDelta_squared U p n b

/-- Categorical exactness of every positive term of the actual Čech complex. -/
theorem manifoldCech_exactAt_succ (n : ℕ) :
    (CechContraction.manifoldCechComplex (E := E) U p).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  change Function.Exact
    ((CechContraction.manifoldCechComplex (E := E) U p).d n (n + 1))
    ((CechContraction.manifoldCechComplex (E := E) U p).d (n + 1) (n + 2))
  rw [CechContraction.manifoldCechComplex_d, CechContraction.manifoldCechComplex_d]
  exact manifoldCech_positive_functionExact U p hcover n

/-- The complete row-exactness package required by the total-complex comparison. -/
theorem manifoldCech_augmented_rows_exact :
    Function.Injective (manifoldCechAugmentation (E := E) U p) ∧
      Function.Exact (manifoldCechAugmentation (E := E) U p)
        (CechContraction.manifoldCechDelta (E := E) U p 0) ∧
      ∀ n : ℕ, (CechContraction.manifoldCechComplex (E := E) U p).ExactAt (n + 1) :=
  ⟨manifoldCechAugmentation_injective U p hcover,
    manifoldCechAugmentation_exact U p hcover,
    manifoldCech_exactAt_succ U p hcover⟩

end

end OAI.Analysis.DifferentialForms.Manifold.CechAugmentation
