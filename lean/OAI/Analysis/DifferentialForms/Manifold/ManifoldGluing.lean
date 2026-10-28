import OAI.Analysis.DifferentialForms.Manifold.Open

/-! # Manifold Gluing -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
Unique gluing of actual tangent-covector-valued smooth sections on a manifold.
The fibers depend on the point; the chosen local section is evaluated at that
same point. Smoothness is obtained from the established local chart criterion.
-/

open Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
    {ι : Type w} {n : ℕ} {U : Opens M} {V : ι → Opens M}

/-- Agreement of the actual tangent covectors on every overlap. -/
def Open.SmoothOpenManifoldForm.Compatible (forms : ∀ i, Open.SmoothOpenManifoldForm E (V i) n) : Prop :=
  ∀ (i j) (x : M) (hi : x ∈ V i) (hj : x ∈ V j),
    forms i ⟨x, hi⟩ = forms j ⟨x, hj⟩

theorem Open.SmoothOpenManifoldForm.compatible_iff_restrict (forms : ∀ i, Open.SmoothOpenManifoldForm E (V i) n) :
    Open.SmoothOpenManifoldForm.Compatible forms ↔ ∀ i j,
      Open.SmoothOpenManifoldForm.restrict (show V i ⊓ V j ≤ V i from inf_le_left) (forms i) =
        Open.SmoothOpenManifoldForm.restrict (show V i ⊓ V j ≤ V j from inf_le_right) (forms j) := by
  constructor
  · intro h i j
    apply Open.SmoothOpenManifoldForm.ext
    intro x
    exact h i j x x.property.1 x.property.2
  · intro h i j x hi hj
    exact congrArg (fun f : Open.SmoothOpenManifoldForm E (V i ⊓ V j) n => f ⟨x, ⟨hi, hj⟩⟩)
      (h i j)

/-- Assemble the dependent tangent covectors by choosing a covering section. -/
def Open.SmoothOpenManifoldForm.glueFunction (hcover : (U : Set M) ⊆ ⋃ i, (V i : Set M))
    (forms : ∀ i, Open.SmoothOpenManifoldForm E (V i) n) : Open.RawOpenManifoldForm E U n :=
  fun x => forms (Classical.choose (Set.mem_iUnion.mp (hcover x.property)))
    ⟨x, Classical.choose_spec (Set.mem_iUnion.mp (hcover x.property))⟩

theorem Open.SmoothOpenManifoldForm.glueFunction_eq (hcover : (U : Set M) ⊆ ⋃ i, (V i : Set M))
    (forms : ∀ i, Open.SmoothOpenManifoldForm E (V i) n) (hcompat : Open.SmoothOpenManifoldForm.Compatible forms)
    (x : U) (i : ι) (hi : (x : M) ∈ V i) :
    Open.SmoothOpenManifoldForm.glueFunction hcover forms x = forms i ⟨x, hi⟩ :=
  hcompat _ i x (Classical.choose_spec (Set.mem_iUnion.mp (hcover x.property))) hi

theorem Open.SmoothOpenManifoldForm.glueFunction_smooth (hsub : ∀ i, V i ≤ U)
    (hcover : (U : Set M) ⊆ ⋃ i, (V i : Set M))
    (forms : ∀ i, Open.SmoothOpenManifoldForm E (V i) n) (hcompat : Open.SmoothOpenManifoldForm.Compatible forms) :
    Algebra.IsSmoothManifoldFormOn (Open.openManifoldFormExtension U (Open.SmoothOpenManifoldForm.glueFunction hcover forms))
      (U : Set M) := by
  have hlocal : ∀ i, Algebra.IsSmoothManifoldFormOn
      (Open.openManifoldFormExtension U (Open.SmoothOpenManifoldForm.glueFunction hcover forms)) (V i : Set M) := by
    intro i
    apply (forms i).smooth.congr
    intro x hx
    calc
      (forms i).extension x = forms i ⟨x, hx⟩ := Open.SmoothOpenManifoldForm.extension_apply (forms i) ⟨x, hx⟩
      _ = Open.SmoothOpenManifoldForm.glueFunction hcover forms ⟨x, hsub i hx⟩ :=
        (Open.SmoothOpenManifoldForm.glueFunction_eq hcover forms hcompat ⟨x, hsub i hx⟩ i hx).symm
      _ = Open.openManifoldFormExtension U (Open.SmoothOpenManifoldForm.glueFunction hcover forms) x :=
        (Open.openManifoldFormExtension_apply U _ ⟨x, hsub i hx⟩).symm
  exact (Algebra.IsSmoothManifoldFormOn.iUnion hlocal (fun i => (V i).isOpen)).mono hcover

/-- The smooth section glued over a covering family of open sets. -/
def Open.SmoothOpenManifoldForm.glue (hsub : ∀ i, V i ≤ U)
    (hcover : (U : Set M) ⊆ ⋃ i, (V i : Set M))
    (forms : ∀ i, Open.SmoothOpenManifoldForm E (V i) n) (hcompat : Open.SmoothOpenManifoldForm.Compatible forms) :
    Open.SmoothOpenManifoldForm E U n :=
  ⟨Open.SmoothOpenManifoldForm.glueFunction hcover forms, Open.SmoothOpenManifoldForm.glueFunction_smooth hsub hcover forms hcompat⟩

theorem Open.SmoothOpenManifoldForm.glue_apply (hsub : ∀ i, V i ≤ U)
    (hcover : (U : Set M) ⊆ ⋃ i, (V i : Set M))
    (forms : ∀ i, Open.SmoothOpenManifoldForm E (V i) n) (hcompat : Open.SmoothOpenManifoldForm.Compatible forms)
    (x : U) (i : ι) (hi : (x : M) ∈ V i) :
    Open.SmoothOpenManifoldForm.glue hsub hcover forms hcompat x = forms i ⟨x, hi⟩ :=
  Open.SmoothOpenManifoldForm.glueFunction_eq hcover forms hcompat x i hi

@[simp]
theorem Open.SmoothOpenManifoldForm.restrict_glue (hsub : ∀ i, V i ≤ U)
    (hcover : (U : Set M) ⊆ ⋃ i, (V i : Set M))
    (forms : ∀ i, Open.SmoothOpenManifoldForm E (V i) n) (hcompat : Open.SmoothOpenManifoldForm.Compatible forms) (i : ι) :
    Open.SmoothOpenManifoldForm.restrict (hsub i) (Open.SmoothOpenManifoldForm.glue hsub hcover forms hcompat) = forms i := by
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  exact Open.SmoothOpenManifoldForm.glue_apply hsub hcover forms hcompat ⟨x, hsub i x.property⟩ i x.property

theorem Open.SmoothOpenManifoldForm.eq_glue_of_restrict_eq (hsub : ∀ i, V i ≤ U)
    (hcover : (U : Set M) ⊆ ⋃ i, (V i : Set M))
    (forms : ∀ i, Open.SmoothOpenManifoldForm E (V i) n) (hcompat : Open.SmoothOpenManifoldForm.Compatible forms)
    (form : Open.SmoothOpenManifoldForm E U n)
    (hform : ∀ i, Open.SmoothOpenManifoldForm.restrict (hsub i) form = forms i) :
    form = Open.SmoothOpenManifoldForm.glue hsub hcover forms hcompat := by
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover x.property)
  have heq := congrArg (fun f : Open.SmoothOpenManifoldForm E (V i) n => f ⟨x, hi⟩) (hform i)
  exact heq.trans (Open.SmoothOpenManifoldForm.glue_apply hsub hcover forms hcompat x i hi).symm

/-- Unique gluing of smooth manifold forms on an arbitrary open cover. -/
theorem Open.SmoothOpenManifoldForm.existsUnique_glue (hsub : ∀ i, V i ≤ U)
    (hcover : (U : Set M) ⊆ ⋃ i, (V i : Set M))
    (forms : ∀ i, Open.SmoothOpenManifoldForm E (V i) n) (hcompat : Open.SmoothOpenManifoldForm.Compatible forms) :
    ∃! form : Open.SmoothOpenManifoldForm E U n, ∀ i, Open.SmoothOpenManifoldForm.restrict (hsub i) form = forms i := by
  refine ⟨Open.SmoothOpenManifoldForm.glue hsub hcover forms hcompat, Open.SmoothOpenManifoldForm.restrict_glue hsub hcover forms hcompat, ?_⟩
  intro form hform
  exact Open.SmoothOpenManifoldForm.eq_glue_of_restrict_eq hsub hcover forms hcompat form hform

theorem Open.SmoothOpenManifoldForm.existsUnique_glue_iSup (forms : ∀ i, Open.SmoothOpenManifoldForm E (V i) n)
    (hcompat : Open.SmoothOpenManifoldForm.Compatible forms) :
    ∃! form : Open.SmoothOpenManifoldForm E (iSup V) n,
      ∀ i, Open.SmoothOpenManifoldForm.restrict (le_iSup V i) form = forms i := by
  apply Open.SmoothOpenManifoldForm.existsUnique_glue (fun i => le_iSup V i) _ forms hcompat
  simpa only [Opens.coe_iSup] using (Subset.rfl : (⋃ i, (V i : Set M)) ⊆ ⋃ i, (V i : Set M))

end

end OAI.Analysis.DifferentialForms.Manifold
