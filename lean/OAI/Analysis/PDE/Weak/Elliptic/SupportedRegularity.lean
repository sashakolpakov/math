import OAI.Analysis.PDE.Weak.Elliptic.GlobalProduct

noncomputable section
open Set _root_.MeasureTheory Filter
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ} {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Global weak derivatives, all supported in the same prescribed set. -/
def SupportedRegularity (K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) :
    ℕ → Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)) → Prop
  | 0, u => ∀ᵐ x ∂volume, x ∉ K → u x = 0
  | k + 1, u => (∀ᵐ x ∂volume, x ∉ K → u x = 0) ∧
      ∀ i : Fin (m + 1), ∃ g : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)),
        HasWeakDirectionalDerivativeOn volume univ (Pi.single i 1) u g ∧
          SupportedRegularity K k g

omit [CompleteSpace E] in
theorem SupportedRegularity.support {K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))} (hu : SupportedRegularity K k u) :
    ∀ᵐ x ∂volume, x ∉ K → u x = 0 := by
  cases k with
  | zero => exact hu
  | succ k => exact hu.1

omit [CompleteSpace E] in
theorem SupportedRegularity.add {K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u v : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hu : SupportedRegularity K k u) (hv : SupportedRegularity K k v) :
    SupportedRegularity K k (u + v) := by
  induction k generalizing u v with
  | zero =>
    filter_upwards [hu.support, hv.support, Lp.coeFn_add u v] with x hx hy hz
    intro hn
    rw [hz, Pi.add_apply, hx hn, hy hn, add_zero]
  | succ k ih =>
    refine ⟨?_, ?_⟩
    · filter_upwards [hu.support, hv.support, Lp.coeFn_add u v] with x hx hy hz
      intro hn
      rw [hz, Pi.add_apply, hx hn, hy hn, add_zero]
    intro i
    obtain ⟨g, hd, hg⟩ := hu.2 i
    obtain ⟨w, he, hw⟩ := hv.2 i
    exact ⟨g + w, hd.add_Lp volume he, ih hg hw⟩

/-- A smooth compactly supported coefficient localizes a finite weak
derivative hierarchy, including the support of every resulting derivative. -/
theorem WeakRegularity.compact_operator_mul
    {Ω K : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {k : ℕ}
    {u : Lp E 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m))}
    (hu : WeakRegularity Ω k u)
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → E →L[ℝ] F) (hA : ContDiff ℝ ∞ A)
    (hs : HasCompactSupport A) (hK : tsupport A ⊆ K) (hΩ : tsupport A ⊆ Ω)
    {M : ℝ} (hM : ∀ x, ‖A x‖ ≤ M) :
    SupportedRegularity K k
      (fieldMultiplierCLM A hA.continuous.aestronglyMeasurable (Eventually.of_forall hM) u) := by
  induction k generalizing A u M with
  | zero =>
    filter_upwards [fieldMultiplierCLM_ae A hA.continuous.aestronglyMeasurable
      (Eventually.of_forall hM) u] with x hx
    intro hn
    rw [hx, image_eq_zero_of_notMem_tsupport (fun h ↦ hn (hK h)), zero_apply]
  | succ k ih =>
    refine ⟨?_, ?_⟩
    · filter_upwards [fieldMultiplierCLM_ae A hA.continuous.aestronglyMeasurable
        (Eventually.of_forall hM) u] with x hx
      intro hn
      rw [hx, image_eq_zero_of_notMem_tsupport (fun h ↦ hn (hK h)), zero_apply]
    intro i
    obtain ⟨g, hd, hg⟩ := hu i
    have hAi := contDiff_coordinateDerivative hA i
    have hAs : HasCompactSupport (coordinateDerivative A i) := hs.fderiv_apply ℝ _
    have hAsub : tsupport (coordinateDerivative A i) ⊆ tsupport A :=
      tsupport_fderiv_apply_subset ℝ _
    obtain ⟨D, hD⟩ := (smoothBounded_of_hasCompactSupport hAi hAs).bound
    let ag := fieldMultiplierCLM A hA.continuous.aestronglyMeasurable (Eventually.of_forall hM) g
    let du := fieldMultiplierCLM (coordinateDerivative A i) hAi.continuous.aestronglyMeasurable
      (Eventually.of_forall hD) u
    refine ⟨ag + du, ?_, ?_⟩
    · have hr := (hd.operator_apply_global volume A (hA.of_le (by simp)) hΩ u g).on (Ω := univ)
      apply OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn.congr_on volume hr
      · filter_upwards [fieldMultiplierCLM_ae A hA.continuous.aestronglyMeasurable
          (Eventually.of_forall hM) u] with x hx
        exact fun _ ↦ hx.symm
      · filter_upwards [fieldMultiplierCLM_ae A hA.continuous.aestronglyMeasurable
          (Eventually.of_forall hM) g,
          fieldMultiplierCLM_ae (coordinateDerivative A i) hAi.continuous.aestronglyMeasurable
            (Eventually.of_forall hD) u, Lp.coeFn_add ag du] with x hx hy hz
        intro _
        rw [hz]
        change A x (g x) + fderiv ℝ A x (Pi.single i 1) (u x) = ag x + du x
        rw [hx, hy]
        rfl
    · exact (ih (u := g) hg A hA hs hK hΩ hM).add
        (ih (u := u) hu.pred (coordinateDerivative A i) hAi hAs
          (hAsub.trans hK) (hAsub.trans hΩ) hD)

end OAI.Analysis.PDE.Weak
