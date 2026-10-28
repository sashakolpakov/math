import OAI.Analysis.DifferentialForms.Manifold.OpenD
import Mathlib.Data.Set.UnionLift

/-! # Gluing -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
Gluing actual smooth differential forms over an open cover. The underlying
function is mathlib's `Set.iUnionLift`; local agreement with the given smooth
functions proves its smoothness. No analytic extension outside the open set is
required.
-/

open Filter Set _root_.TopologicalSpace
open scoped _root_.Topology ContDiff

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {U : Opens E} {V : ι → Opens E}

/-- Pointwise agreement of actual forms on every pairwise overlap. -/
def OpenD.SmoothOpenForm.Compatible (forms : ∀ i, OpenD.SmoothOpenForm (V i) n) : Prop :=
  ∀ (i j) (x : E) (hi : x ∈ V i) (hj : x ∈ V j),
    forms i ⟨x, hi⟩ = forms j ⟨x, hj⟩

theorem OpenD.SmoothOpenForm.compatible_iff_restrict (forms : ∀ i, OpenD.SmoothOpenForm (V i) n) :
    OpenD.SmoothOpenForm.Compatible forms ↔ ∀ i j,
      OpenD.SmoothOpenForm.restrict (show V i ⊓ V j ≤ V i from inf_le_left) (forms i) =
        OpenD.SmoothOpenForm.restrict (show V i ⊓ V j ≤ V j from inf_le_right) (forms j) := by
  constructor
  · intro h i j
    apply OpenD.SmoothOpenForm.ext
    intro x
    exact h i j x x.property.1 x.property.2
  · intro h i j x hi hj
    exact congrArg (fun f : OpenD.SmoothOpenForm (V i ⊓ V j) n => f ⟨x, ⟨hi, hj⟩⟩) (h i j)

/-- Glue the coefficient functions on a cover, before recording smoothness. -/
def OpenD.SmoothOpenForm.glueFunction (hcover : (U : Set E) ⊆ ⋃ i, (V i : Set E))
    (forms : ∀ i, OpenD.SmoothOpenForm (V i) n) (hcompat : OpenD.SmoothOpenForm.Compatible forms) :
    U → Basic.FormValue E n :=
  Set.iUnionLift (fun i => (V i : Set E)) (fun i => (forms i : V i → Basic.FormValue E n))
    hcompat (U : Set E) hcover

theorem OpenD.SmoothOpenForm.glueFunction_eq (hcover : (U : Set E) ⊆ ⋃ i, (V i : Set E))
    (forms : ∀ i, OpenD.SmoothOpenForm (V i) n) (hcompat : OpenD.SmoothOpenForm.Compatible forms)
    (x : U) (i : ι) (hi : (x : E) ∈ V i) :
    OpenD.SmoothOpenForm.glueFunction hcover forms hcompat x = forms i ⟨x, hi⟩ :=
  Set.iUnionLift_of_mem (S := fun i => (V i : Set E))
    (f := fun i => (forms i : V i → Basic.FormValue E n)) (hf := hcompat) (hT := hcover) x hi

theorem OpenD.SmoothOpenForm.glueFunction_smooth (hsub : ∀ i, V i ≤ U)
    (hcover : (U : Set E) ⊆ ⋃ i, (V i : Set E))
    (forms : ∀ i, OpenD.SmoothOpenForm (V i) n) (hcompat : OpenD.SmoothOpenForm.Compatible forms) :
    ContDiffOn ℝ ∞ (OpenD.openFormExtension U (OpenD.SmoothOpenForm.glueFunction hcover forms hcompat)) (U : Set E) := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
  have hsmooth : ContDiffAt ℝ ∞ (forms i).extension x :=
    (forms i).smooth.contDiffAt ((V i).isOpen.mem_nhds hi)
  apply ContDiffAt.contDiffWithinAt
  apply hsmooth.congr_of_eventuallyEq
  filter_upwards [(V i).isOpen.mem_nhds hi] with y hy
  calc
    OpenD.openFormExtension U (OpenD.SmoothOpenForm.glueFunction hcover forms hcompat) y =
        OpenD.SmoothOpenForm.glueFunction hcover forms hcompat ⟨y, hsub i hy⟩ :=
      OpenD.openFormExtension_apply U _ ⟨y, hsub i hy⟩
    _ = forms i ⟨y, hy⟩ := OpenD.SmoothOpenForm.glueFunction_eq hcover forms hcompat _ i hy
    _ = (forms i).extension y := (OpenD.SmoothOpenForm.extension_apply (forms i) ⟨y, hy⟩).symm

/-- The unique smooth form obtained by gluing a compatible family. -/
def OpenD.SmoothOpenForm.glue (hsub : ∀ i, V i ≤ U)
    (hcover : (U : Set E) ⊆ ⋃ i, (V i : Set E))
    (forms : ∀ i, OpenD.SmoothOpenForm (V i) n) (hcompat : OpenD.SmoothOpenForm.Compatible forms) :
    OpenD.SmoothOpenForm U n :=
  ⟨OpenD.SmoothOpenForm.glueFunction hcover forms hcompat, OpenD.SmoothOpenForm.glueFunction_smooth hsub hcover forms hcompat⟩

theorem OpenD.SmoothOpenForm.glue_apply (hsub : ∀ i, V i ≤ U)
    (hcover : (U : Set E) ⊆ ⋃ i, (V i : Set E))
    (forms : ∀ i, OpenD.SmoothOpenForm (V i) n) (hcompat : OpenD.SmoothOpenForm.Compatible forms)
    (x : U) (i : ι) (hi : (x : E) ∈ V i) :
    OpenD.SmoothOpenForm.glue hsub hcover forms hcompat x = forms i ⟨x, hi⟩ :=
  OpenD.SmoothOpenForm.glueFunction_eq hcover forms hcompat x i hi

@[simp]
theorem OpenD.SmoothOpenForm.restrict_glue (hsub : ∀ i, V i ≤ U)
    (hcover : (U : Set E) ⊆ ⋃ i, (V i : Set E))
    (forms : ∀ i, OpenD.SmoothOpenForm (V i) n) (hcompat : OpenD.SmoothOpenForm.Compatible forms) (i : ι) :
    OpenD.SmoothOpenForm.restrict (hsub i) (OpenD.SmoothOpenForm.glue hsub hcover forms hcompat) = forms i := by
  apply OpenD.SmoothOpenForm.ext
  intro x
  exact OpenD.SmoothOpenForm.glue_apply hsub hcover forms hcompat ⟨x, hsub i x.property⟩ i x.property

theorem OpenD.SmoothOpenForm.eq_glue_of_restrict_eq (hsub : ∀ i, V i ≤ U)
    (hcover : (U : Set E) ⊆ ⋃ i, (V i : Set E))
    (forms : ∀ i, OpenD.SmoothOpenForm (V i) n) (hcompat : OpenD.SmoothOpenForm.Compatible forms)
    (form : OpenD.SmoothOpenForm U n) (hform : ∀ i, OpenD.SmoothOpenForm.restrict (hsub i) form = forms i) :
    form = OpenD.SmoothOpenForm.glue hsub hcover forms hcompat := by
  apply OpenD.SmoothOpenForm.ext
  intro x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover x.property)
  have heq := congrArg (fun f : OpenD.SmoothOpenForm (V i) n => f ⟨x, hi⟩) (hform i)
  exact heq.trans (OpenD.SmoothOpenForm.glue_apply hsub hcover forms hcompat x i hi).symm

/-- Existence and uniqueness of gluing for an arbitrary open cover. -/
theorem OpenD.SmoothOpenForm.existsUnique_glue (hsub : ∀ i, V i ≤ U)
    (hcover : (U : Set E) ⊆ ⋃ i, (V i : Set E))
    (forms : ∀ i, OpenD.SmoothOpenForm (V i) n) (hcompat : OpenD.SmoothOpenForm.Compatible forms) :
    ∃! form : OpenD.SmoothOpenForm U n, ∀ i, OpenD.SmoothOpenForm.restrict (hsub i) form = forms i := by
  refine ⟨OpenD.SmoothOpenForm.glue hsub hcover forms hcompat, OpenD.SmoothOpenForm.restrict_glue hsub hcover forms hcompat, ?_⟩
  intro form hform
  exact OpenD.SmoothOpenForm.eq_glue_of_restrict_eq hsub hcover forms hcompat form hform

/-- The open-supremum formulation of the smooth-form sheaf gluing property. -/
theorem OpenD.SmoothOpenForm.existsUnique_glue_iSup (forms : ∀ i, OpenD.SmoothOpenForm (V i) n)
    (hcompat : OpenD.SmoothOpenForm.Compatible forms) :
    ∃! form : OpenD.SmoothOpenForm (iSup V) n,
      ∀ i, OpenD.SmoothOpenForm.restrict (le_iSup V i) form = forms i := by
  apply OpenD.SmoothOpenForm.existsUnique_glue (fun i => le_iSup V i) _ forms hcompat
  simpa only [Opens.coe_iSup] using (Subset.rfl : (⋃ i, (V i : Set E)) ⊆ ⋃ i, (V i : Set E))

end

end OAI.Analysis.DifferentialForms.Manifold
