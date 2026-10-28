import OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechLocallyFinite
import OAI.AlgebraicTopology.DeRham.Comparison.RelativePartitionFormOperators
import OAI.AlgebraicTopology.DeRham.Comparison.RelativeSmoothPartition

/-! # Relative Smooth Cech -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.RelativeSmoothCech

noncomputable section

/-!
# Smooth Čech contraction on an arbitrary open domain

These operators use a genuine smooth partition on the induced manifold of
the covered open set. Local finiteness and support are intrinsic to that open
set, allowing accumulation at its ambient boundary.
-/

open _root_.TopologicalSpace Function Set
open scoped _root_.Manifold ContDiff BigOperators

universe u

variable {E ι : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (W : Opens E) (cover : ι → Opens E) (p : ℕ)
variable (rho : SmoothPartitionOfUnity ι 𝓘(ℝ, E) W univ)
  (hsub : rho.IsSubordinate (fun i => {x : W | (x : E) ∈ cover i}))

/-- An actual intrinsic partition supplies a supported extension onto each subdomain. -/
def relativeCechPartitionOperator (V : Opens E) (hVW : V ≤ W) (i : ι) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (cover i ⊓ V) p →ₗ[ℂ] Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V p :=
  RelativePartitionFormOperators.relativeSupportedFormExtension (RelativeSmoothPartition.relativePartitionWeight rho i)
    (RelativeSmoothPartition.relativePartitionWeight_smooth rho i)
    (RelativeSmoothPartition.relativePartitionWeight_tsupport_subset rho cover hsub i) hVW

theorem relativeCechPartitionOperator_apply (V : Opens E) (hVW : V ≤ W) (i : ι)
    (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (cover i ⊓ V) p) (x : V) :
    relativeCechPartitionOperator W cover p rho hsub V hVW i form x =
      RelativeSmoothPartition.relativePartitionWeight rho i x • form.extension x := rfl

theorem relativeCechPartitionOperator_restricted_apply (V : Opens E) (hVW : V ≤ W) (i : ι)
    (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V p) (x : V) :
    relativeCechPartitionOperator W cover p rho hsub V hVW i
      (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict inf_le_right form) x =
        RelativeSmoothPartition.relativePartitionWeight rho i x • form x :=
  RelativePartitionFormOperators.relativeSupportedFormExtension_restricted_apply (RelativeSmoothPartition.relativePartitionWeight rho i)
    (RelativeSmoothPartition.relativePartitionWeight_smooth rho i)
    (RelativeSmoothPartition.relativePartitionWeight_tsupport_subset rho cover hsub i) hVW form x

theorem relativeCechPartitionOperator_restrict {V V' : Opens E}
    (hVW : V ≤ W) (hV'V : V' ≤ V) (i : ι) (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (cover i ⊓ V) p) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict hV'V (relativeCechPartitionOperator W cover p rho hsub V hVW i form) =
      relativeCechPartitionOperator W cover p rho hsub V' (hV'V.trans hVW) i
        (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (inf_le_inf_left (cover i) hV'V) form) :=
  RelativePartitionFormOperators.relativeSupportedFormExtension_restrict (RelativeSmoothPartition.relativePartitionWeight rho i)
    (RelativeSmoothPartition.relativePartitionWeight_smooth rho i)
    (RelativeSmoothPartition.relativePartitionWeight_tsupport_subset rho cover hsub i) hVW hV'V form

variable (hcoverW : ∀ i, cover i ≤ W)

include hcoverW in
omit [NormedSpace ℝ E] in
/-- Every nonempty Čech intersection lies in the open domain being covered. -/
theorem cechIntersection_le_open {n : ℕ} (a : Fin (n + 1) → ι) :
    SmoothCech.cechIntersection cover a ≤ W :=
  (SmoothCech.cechIntersection_le cover a 0).trans (hcoverW (a 0))

/-- Weighted insertion using the intrinsic partition and the proved relative extension. -/
def relativeCechWeightedInsertion (n : ℕ) (i : ι) :
    SmoothCech.SmoothCechCochain cover p (n + 1) →ₗ[ℂ] SmoothCech.SmoothCechCochain cover p n where
  toFun c a := relativeCechPartitionOperator W cover p rho hsub
    (SmoothCech.cechIntersection cover a) (cechIntersection_le_open W cover hcoverW a) i
    (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (le_of_eq (SmoothCech.cechIntersection_cons cover i a).symm)
      (c (Fin.cons i a)))
  map_add' c d := by
    funext a
    exact ((relativeCechPartitionOperator W cover p rho hsub
      (SmoothCech.cechIntersection cover a) (cechIntersection_le_open W cover hcoverW a) i).comp
      (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (le_of_eq (SmoothCech.cechIntersection_cons cover i a).symm))).map_add
        (c (Fin.cons i a)) (d (Fin.cons i a))
  map_smul' z c := by
    funext a
    exact ((relativeCechPartitionOperator W cover p rho hsub
      (SmoothCech.cechIntersection cover a) (cechIntersection_le_open W cover hcoverW a) i).comp
      (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (le_of_eq (SmoothCech.cechIntersection_cons cover i a).symm))).map_smul
        z (c (Fin.cons i a))

theorem relativeCechWeightedInsertion_coface_zero (n : ℕ) (i : ι)
    (c : SmoothCech.SmoothCechCochain cover p n) (a : Fin (n + 1) → ι) :
    relativeCechWeightedInsertion W cover p rho hsub hcoverW n i
        (SmoothCechPartition.smoothCechCoface cover p n 0 c) a =
      relativeCechPartitionOperator W cover p rho hsub (SmoothCech.cechIntersection cover a)
        (cechIntersection_le_open W cover hcoverW a) i
        (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict inf_le_right (c a)) := by
  change ((a : Fin (n + 1) → ι) → Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (SmoothCech.cechIntersection cover a) p) at c
  change relativeCechPartitionOperator W cover p rho hsub (SmoothCech.cechIntersection cover a)
    (cechIntersection_le_open W cover hcoverW a) i
    (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (le_of_eq (SmoothCech.cechIntersection_cons cover i a).symm)
      (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict
        (SmoothCech.cechIntersection_le_precomp cover (Fin.cons i a) Fin.succ)
        (c (Fin.cons i a ∘ Fin.succ)))) = _
  simp only [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_trans]
  apply congrArg
  exact SmoothCechPartition.smoothCechSection_congr cover p n c (Fin.cons_comp_succ i a) _ _ _

theorem relativeCechWeightedInsertion_coface_succ (n : ℕ) (i : ι) (j : Fin (n + 2))
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) :
    relativeCechWeightedInsertion W cover p rho hsub hcoverW (n + 1) i
        (SmoothCechPartition.smoothCechCoface cover p (n + 1) j.succ c) =
      SmoothCechPartition.smoothCechCoface cover p n j
        (relativeCechWeightedInsertion W cover p rho hsub hcoverW n i c) := by
  change ((a : Fin (n + 2) → ι) → Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (SmoothCech.cechIntersection cover a) p) at c
  funext a
  change relativeCechPartitionOperator W cover p rho hsub (SmoothCech.cechIntersection cover a)
      (cechIntersection_le_open W cover hcoverW a) i
      (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (le_of_eq (SmoothCech.cechIntersection_cons cover i a).symm)
        (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict
          (SmoothCech.cechIntersection_le_precomp cover (Fin.cons i a) j.succ.succAbove)
          (c (Fin.cons i a ∘ j.succ.succAbove)))) =
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (SmoothCech.cechIntersection_le_precomp cover a j.succAbove)
      (relativeCechPartitionOperator W cover p rho hsub (SmoothCech.cechIntersection cover (a ∘ j.succAbove))
        (cechIntersection_le_open W cover hcoverW (a ∘ j.succAbove)) i
        (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict
          (le_of_eq (SmoothCech.cechIntersection_cons cover i (a ∘ j.succAbove)).symm)
          (c (Fin.cons i (a ∘ j.succAbove)))))
  rw [relativeCechPartitionOperator_restrict]
  simp only [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_trans]
  apply congrArg
  exact SmoothCechPartition.smoothCechSection_congr cover p (n + 1) c
    (Fin.cons_comp_succ_succAbove i a j) _ _ _

/-- Relative weighted insertion has support inside the corresponding actual scalar support. -/
theorem relativeCechWeightedInsertion_support_subset (n : ℕ) (i : ι)
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) (a : Fin (n + 1) → ι) :
    support (fun x : SmoothCech.cechIntersection cover a => SmoothCechLocallyFinite.smoothCechEvaluation cover p n a x
      (relativeCechWeightedInsertion W cover p rho hsub hcoverW n i c)) ⊆
        support (fun x : SmoothCech.cechIntersection cover a => RelativeSmoothPartition.relativePartitionWeight rho i x) := by
  intro x hx
  change RelativeSmoothPartition.relativePartitionWeight rho i x ≠ 0
  intro hz
  apply hx
  change RelativeSmoothPartition.relativePartitionWeight rho i x •
    (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (le_of_eq (SmoothCech.cechIntersection_cons cover i a).symm)
      (c (Fin.cons i a))).extension x = 0
  rw [hz]
  exact zero_smul ℝ ((Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (n := p)
    (le_of_eq (SmoothCech.cechIntersection_cons cover i a).symm) (c (Fin.cons i a))).extension (x : E))

/-- Local finiteness is needed and proved only within the recipient open intersection. -/
theorem relativeCechWeightedInsertion_locallyFinite (n : ℕ)
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) (a : Fin (n + 1) → ι) :
    LocallyFinite (fun i => support (fun x : SmoothCech.cechIntersection cover a =>
      SmoothCechLocallyFinite.smoothCechEvaluation cover p n a x
        (relativeCechWeightedInsertion W cover p rho hsub hcoverW n i c))) := by
  exact (RelativeSmoothPartition.relativePartitionWeight_locallyFinite_on rho
    (cechIntersection_le_open W cover hcoverW a)).subset
      (fun i => relativeCechWeightedInsertion_support_subset W cover p rho hsub hcoverW n i c a)

theorem relativeCechWeightedInsertion_finite_support (n : ℕ)
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) (a : Fin (n + 1) → ι)
    (x : SmoothCech.cechIntersection cover a) :
    HasFiniteSupport (fun i => SmoothCechLocallyFinite.smoothCechEvaluation cover p n a x
      (relativeCechWeightedInsertion W cover p rho hsub hcoverW n i c)) :=
  (relativeCechWeightedInsertion_locallyFinite W cover p rho hsub hcoverW n c a).point_finite x

/-- Sum the actual relative weighted insertions by the proved open-domain smooth sum theorem. -/
def relativeCechInsertion (n : ℕ) (c : SmoothCech.SmoothCechCochain cover p (n + 1)) :
    SmoothCech.SmoothCechCochain cover p n :=
  fun a => Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.locallyFiniteSum
    (fun i => relativeCechWeightedInsertion W cover p rho hsub hcoverW n i c a)
    (relativeCechWeightedInsertion_locallyFinite W cover p rho hsub hcoverW n c a)

theorem relativeCechInsertion_apply (n : ℕ) (c : SmoothCech.SmoothCechCochain cover p (n + 1))
    (a : Fin (n + 1) → ι) (x : SmoothCech.cechIntersection cover a) :
    SmoothCechLocallyFinite.smoothCechEvaluation cover p n a x (relativeCechInsertion W cover p rho hsub hcoverW n c) =
      ∑ᶠ i, SmoothCechLocallyFinite.smoothCechEvaluation cover p n a x
        (relativeCechWeightedInsertion W cover p rho hsub hcoverW n i c) :=
  Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.locallyFiniteSum_apply
    (fun i => relativeCechWeightedInsertion W cover p rho hsub hcoverW n i c a)
    (relativeCechWeightedInsertion_locallyFinite W cover p rho hsub hcoverW n c a) x

theorem relativeCechInsertion_add (n : ℕ) (c d : SmoothCech.SmoothCechCochain cover p (n + 1)) :
    relativeCechInsertion W cover p rho hsub hcoverW n (c + d) =
      relativeCechInsertion W cover p rho hsub hcoverW n c +
        relativeCechInsertion W cover p rho hsub hcoverW n d := by
  funext a
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  change SmoothCechLocallyFinite.smoothCechEvaluation cover p n a x
      (relativeCechInsertion W cover p rho hsub hcoverW n (c + d)) =
    SmoothCechLocallyFinite.smoothCechEvaluation cover p n a x (relativeCechInsertion W cover p rho hsub hcoverW n c) +
      SmoothCechLocallyFinite.smoothCechEvaluation cover p n a x (relativeCechInsertion W cover p rho hsub hcoverW n d)
  rw [relativeCechInsertion_apply, relativeCechInsertion_apply, relativeCechInsertion_apply]
  exact (finsum_congr (fun i => ((SmoothCechLocallyFinite.smoothCechEvaluation cover p n a x).comp
    (relativeCechWeightedInsertion W cover p rho hsub hcoverW n i)).map_add c d)).trans
      (finsum_add_distrib
        (relativeCechWeightedInsertion_finite_support W cover p rho hsub hcoverW n c a x)
        (relativeCechWeightedInsertion_finite_support W cover p rho hsub hcoverW n d a x))

theorem relativeCechInsertion_smul (n : ℕ) (z : ℂ) (c : SmoothCech.SmoothCechCochain cover p (n + 1)) :
    relativeCechInsertion W cover p rho hsub hcoverW n (z • c) =
      z • relativeCechInsertion W cover p rho hsub hcoverW n c := by
  funext a
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  change SmoothCechLocallyFinite.smoothCechEvaluation cover p n a x
      (relativeCechInsertion W cover p rho hsub hcoverW n (z • c)) =
    z • SmoothCechLocallyFinite.smoothCechEvaluation cover p n a x (relativeCechInsertion W cover p rho hsub hcoverW n c)
  rw [relativeCechInsertion_apply, relativeCechInsertion_apply]
  exact (finsum_congr (fun i => ((SmoothCechLocallyFinite.smoothCechEvaluation cover p n a x).comp
    (relativeCechWeightedInsertion W cover p rho hsub hcoverW n i)).map_smul z c)).trans
      (smul_finsum' z
        (relativeCechWeightedInsertion_finite_support W cover p rho hsub hcoverW n c a x)).symm

/-- The genuine partition homotopy on smooth forms over a cover of W. -/
def relativeCechHomotopy (n : ℕ) :
    SmoothCech.SmoothCechCochain cover p (n + 1) →ₗ[ℂ] SmoothCech.SmoothCechCochain cover p n where
  toFun := relativeCechInsertion W cover p rho hsub hcoverW n
  map_add' := relativeCechInsertion_add W cover p rho hsub hcoverW n
  map_smul' := relativeCechInsertion_smul W cover p rho hsub hcoverW n

theorem relativeCechHomotopy_apply (n : ℕ) (c : SmoothCech.SmoothCechCochain cover p (n + 1))
    (a : Fin (n + 1) → ι) (x : SmoothCech.cechIntersection cover a) :
    SmoothCechLocallyFinite.smoothCechEvaluation cover p n a x (relativeCechHomotopy W cover p rho hsub hcoverW n c) =
      ∑ᶠ i, SmoothCechLocallyFinite.smoothCechEvaluation cover p n a x
        (relativeCechWeightedInsertion W cover p rho hsub hcoverW n i c) :=
  relativeCechInsertion_apply W cover p rho hsub hcoverW n c a x

theorem relativeCechHomotopy_coface_zero (n : ℕ) (c : SmoothCech.SmoothCechCochain cover p n) :
    relativeCechHomotopy W cover p rho hsub hcoverW n (SmoothCechPartition.smoothCechCoface cover p n 0 c) = c := by
  funext a
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  change SmoothCechLocallyFinite.smoothCechEvaluation cover p n a x
      (relativeCechHomotopy W cover p rho hsub hcoverW n (SmoothCechPartition.smoothCechCoface cover p n 0 c)) =
    SmoothCechLocallyFinite.smoothCechEvaluation cover p n a x c
  rw [relativeCechHomotopy_apply]
  have hterm (i : ι) : SmoothCechLocallyFinite.smoothCechEvaluation cover p n a x
      (relativeCechWeightedInsertion W cover p rho hsub hcoverW n i
        (SmoothCechPartition.smoothCechCoface cover p n 0 c)) =
          RelativeSmoothPartition.relativePartitionWeight rho i x • SmoothCechLocallyFinite.smoothCechEvaluation cover p n a x c := by
    exact (congrArg (PartitionFormOperators.openFormEvaluation x)
      (relativeCechWeightedInsertion_coface_zero W cover p rho hsub hcoverW n i c a)).trans
        (relativeCechPartitionOperator_restricted_apply W cover p rho hsub (SmoothCech.cechIntersection cover a)
          (cechIntersection_le_open W cover hcoverW a) i (c a) x)
  have hsum : (∑ᶠ i, RelativeSmoothPartition.relativePartitionWeight rho i (x : E)) = 1 :=
    RelativeSmoothPartition.relativePartitionWeight_finsum rho
      ⟨(x : E), cechIntersection_le_open W cover hcoverW a x.property⟩
  rw [finsum_congr hterm,
    ← finsum_smul' ((RelativeSmoothPartition.relativePartitionWeight_locallyFinite_on rho
      (cechIntersection_le_open W cover hcoverW a)).point_finite x), hsum, one_smul]

theorem relativeCechHomotopy_coface_succ (n : ℕ) (j : Fin (n + 2))
    (c : SmoothCech.SmoothCechCochain cover p (n + 1)) :
    relativeCechHomotopy W cover p rho hsub hcoverW (n + 1)
        (SmoothCechPartition.smoothCechCoface cover p (n + 1) j.succ c) =
      SmoothCechPartition.smoothCechCoface cover p n j (relativeCechHomotopy W cover p rho hsub hcoverW n c) := by
  funext a
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  change SmoothCechLocallyFinite.smoothCechEvaluation cover p (n + 1) a x
      (relativeCechHomotopy W cover p rho hsub hcoverW (n + 1)
        (SmoothCechPartition.smoothCechCoface cover p (n + 1) j.succ c)) =
    SmoothCechLocallyFinite.smoothCechEvaluation cover p (n + 1) a x
      (SmoothCechPartition.smoothCechCoface cover p n j (relativeCechHomotopy W cover p rho hsub hcoverW n c))
  rw [relativeCechHomotopy_apply, SmoothCechLocallyFinite.smoothCechEvaluation_coface, relativeCechHomotopy_apply]
  apply finsum_congr
  intro i
  exact (congrArg (SmoothCechLocallyFinite.smoothCechEvaluation cover p (n + 1) a x)
    (relativeCechWeightedInsertion_coface_succ W cover p rho hsub hcoverW n i j c)).trans
      (SmoothCechLocallyFinite.smoothCechEvaluation_coface cover p n j a x
        (relativeCechWeightedInsertion W cover p rho hsub hcoverW n i c))

/-- The signed cancellation identity holds on W, irrespective of its ambient boundary. -/
theorem relativeCechHomotopy_delta (n : ℕ) (c : SmoothCech.SmoothCechCochain cover p (n + 1)) :
    relativeCechHomotopy W cover p rho hsub hcoverW (n + 1) (SmoothCech.smoothCechDelta cover p (n + 1) c) =
      c - SmoothCech.smoothCechDelta cover p n (relativeCechHomotopy W cover p rho hsub hcoverW n c) := by
  rw [SmoothCechPartition.smoothCechDelta_eq_sum_coface, map_sum]
  simp only [map_zsmul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    relativeCechHomotopy_coface_zero, relativeCechHomotopy_coface_succ]
  rw [sub_eq_add_neg, SmoothCechPartition.smoothCechDelta_eq_sum_coface, ← Finset.sum_neg_distrib]
  apply congrArg (fun z => c + z)
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ, mul_smul, neg_one_smul, smul_neg]

/-- Positive-degree contraction of the actual smooth Čech complex for the relative partition. -/
theorem relativeCech_contraction (n : ℕ) (c : SmoothCech.SmoothCechCochain cover p (n + 1)) :
    SmoothCech.smoothCechDelta cover p n (relativeCechHomotopy W cover p rho hsub hcoverW n c) +
      relativeCechHomotopy W cover p rho hsub hcoverW (n + 1)
        (SmoothCech.smoothCechDelta cover p (n + 1) c) = c := by
  rw [relativeCechHomotopy_delta]
  abel

theorem relativeCechDelta_homotopy_of_cycle (n : ℕ) (c : SmoothCech.SmoothCechCochain cover p (n + 1))
    (hc : SmoothCech.smoothCechDelta cover p (n + 1) c = 0) :
    SmoothCech.smoothCechDelta cover p n (relativeCechHomotopy W cover p rho hsub hcoverW n c) = c := by
  have h := relativeCech_contraction W cover p rho hsub hcoverW n c
  rw [hc, map_zero, add_zero] at h
  exact h

include rho hsub hcoverW in
/-- Exactness with a specified genuine relative partition. -/
theorem relativeCechDelta_range_eq_ker (n : ℕ) :
    LinearMap.range (SmoothCech.smoothCechDelta cover p n) =
      LinearMap.ker (SmoothCech.smoothCechDelta cover p (n + 1)) := by
  apply le_antisymm
  · rintro c ⟨b, rfl⟩
    exact SmoothCech.smoothCechDelta_squared cover p n b
  · intro c hc
    exact ⟨relativeCechHomotopy W cover p rho hsub hcoverW n c,
      relativeCechDelta_homotopy_of_cycle W cover p rho hsub hcoverW n c hc⟩

include hcoverW in
/-- Every open cover of an open finite-dimensional domain has exact positive smooth Čech rows. -/
theorem smoothCechDelta_range_eq_ker_of_open_cover [FiniteDimensional ℝ E]
    (hcover : ∀ x : W, ∃ i, (x : E) ∈ cover i) (n : ℕ) :
    LinearMap.range (SmoothCech.smoothCechDelta cover p n) =
      LinearMap.ker (SmoothCech.smoothCechDelta cover p (n + 1)) := by
  obtain ⟨partition, hpartition⟩ := RelativeSmoothPartition.exists_relative_smooth_partition W cover hcover
  exact relativeCechDelta_range_eq_ker W cover p partition hpartition hcoverW n

end

end OAI.AlgebraicTopology.DeRham.Comparison.RelativeSmoothCech
