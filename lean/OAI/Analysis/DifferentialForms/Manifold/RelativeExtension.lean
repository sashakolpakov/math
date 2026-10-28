import OAI.Analysis.DifferentialForms.Manifold.SupportedExtension

/-! # Relative Extension -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
# Supported extension inside an open manifold domain

For a scalar supported in `U`, a form on `U ∩ V` extends after multiplication
to a form on `V`. This is the relative version required for partition operators
on intersections of an open cover.
-/

open Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {n : ℕ}

section

/-- Only support inside the target domain matters for relative extension. -/
theorem Algebra.IsSmoothManifoldFormOn.smulFunction_on_of_tsupport_inter_subset {f : M → ℂ}
    {form : Algebra.RawManifoldForm E M n} {W V : Set M}
    (hform : Algebra.IsSmoothManifoldFormOn form W) (hW : IsOpen W) (hV : IsOpen V)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f V)
    (hsupp : tsupport f ∩ V ⊆ W) :
    Algebra.IsSmoothManifoldFormOn (Algebra.RawManifoldForm.smulFunction f form) V := by
  let domains : Bool → Set M :=
    fun b => if b then W ∩ V else (tsupport f)ᶜ ∩ V
  have hlocal : ∀ b, Algebra.IsSmoothManifoldFormOn
      (Algebra.RawManifoldForm.smulFunction f form) (domains b) := by
    intro b
    cases b
    · apply (Algebra.IsSmoothManifoldFormOn.zero (E := E) (n := n) (domains false)).congr
      intro x hx
      have hx' : x ∉ tsupport f := hx.1
      change 0 = f x • form x
      rw [image_eq_zero_of_notMem_tsupport hx']
      exact (zero_smul ℂ (form x)).symm
    · exact (hform.mono inter_subset_left).smulFunction (hf.mono inter_subset_right)
  have hopen : ∀ b, IsOpen (domains b) := by
    intro b
    cases b
    · exact (isClosed_tsupport f).isOpen_compl.inter hV
    · exact hW.inter hV
  have hcover : (⋃ b, domains b) = V := by
    ext x
    constructor
    · intro hx
      obtain ⟨b, hb⟩ := mem_iUnion.mp hx
      cases b <;> exact hb.2
    · intro hx
      by_cases hs : x ∈ tsupport f
      · exact mem_iUnion.mpr ⟨true, hsupp ⟨hs, hx⟩, hx⟩
      · exact mem_iUnion.mpr ⟨false, hs, hx⟩
  rw [← hcover]
  exact Algebra.IsSmoothManifoldFormOn.iUnion hlocal hopen

end

/-- Multiply on `U ∩ V` by a scalar supported in `U` and extend to `V`. -/
def Open.SmoothOpenManifoldForm.supportedExtensionTo (U V : Opens M) (f : M → ℂ)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f (V : Set M))
    (hsupp : tsupport f ⊆ (U : Set M)) :
    Open.SmoothOpenManifoldForm E (U ⊓ V) n →ₗ[ℂ] Open.SmoothOpenManifoldForm E V n where
  toFun form := Open.SmoothOpenManifoldForm.ofRaw V (Algebra.RawManifoldForm.smulFunction f form.extension)
    (form.smooth.smulFunction_on_of_tsupport_inter_subset (U ⊓ V).isOpen V.isOpen
      hf (fun _ hx => ⟨hsupp hx.1, hx.2⟩))
  map_add' form other := by
    apply Open.SmoothOpenManifoldForm.ext
    intro x
    change f x • (form + other).extension x =
      f x • form.extension x + f x • other.extension x
    rw [Open.SmoothOpenManifoldForm.extension_add]
    exact smul_add (f x) (form.extension x) (other.extension x)
  map_smul' c form := by
    apply Open.SmoothOpenManifoldForm.ext
    intro x
    change f x • (c • form).extension x = c • (f x • form.extension x)
    rw [Open.SmoothOpenManifoldForm.extension_smul]
    exact smul_comm (f x) c (form.extension x)

@[simp]
theorem Open.SmoothOpenManifoldForm.supportedExtensionTo_apply (U V : Opens M) (f : M → ℂ)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f (V : Set M))
    (hsupp : tsupport f ⊆ (U : Set M))
    (form : Open.SmoothOpenManifoldForm E (U ⊓ V) n) (x : V) :
    Open.SmoothOpenManifoldForm.supportedExtensionTo U V f hf hsupp form x = f x • form.extension x := rfl

/-- On the original intersection this is pointwise scalar multiplication. -/
theorem Open.SmoothOpenManifoldForm.supportedExtensionTo_apply_mem (U V : Opens M) (f : M → ℂ)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f (V : Set M))
    (hsupp : tsupport f ⊆ (U : Set M))
    (form : Open.SmoothOpenManifoldForm E (U ⊓ V) n) (x : V) (hx : (x : M) ∈ U) :
    Open.SmoothOpenManifoldForm.supportedExtensionTo U V f hf hsupp form x =
      f x • form ⟨x, hx, x.property⟩ := by
  rw [Open.SmoothOpenManifoldForm.supportedExtensionTo_apply]
  exact congrArg (fun z => f x • z) (Open.SmoothOpenManifoldForm.extension_apply form ⟨x, hx, x.property⟩)

/-- The relative extension is zero off the scalar's topological support. -/
theorem Open.SmoothOpenManifoldForm.supportedExtensionTo_eq_zero_of_notMem_tsupport (U V : Opens M) (f : M → ℂ)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f (V : Set M))
    (hsupp : tsupport f ⊆ (U : Set M))
    (form : Open.SmoothOpenManifoldForm E (U ⊓ V) n) (x : V) (hx : (x : M) ∉ tsupport f) :
    Open.SmoothOpenManifoldForm.supportedExtensionTo U V f hf hsupp form x = 0 := by
  rw [Open.SmoothOpenManifoldForm.supportedExtensionTo_apply, image_eq_zero_of_notMem_tsupport hx]
  exact zero_smul ℂ (form.extension x)

/-- Extending inside an open domain commutes with restricting that domain. -/
theorem Open.SmoothOpenManifoldForm.restrict_supportedExtensionTo (U : Opens M) {V W : Opens M} (h : W ≤ V)
    (f : M → ℂ) (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f (V : Set M))
    (hsupp : tsupport f ⊆ (U : Set M))
    (form : Open.SmoothOpenManifoldForm E (U ⊓ V) n) :
    Open.SmoothOpenManifoldForm.restrict h (Open.SmoothOpenManifoldForm.supportedExtensionTo U V f hf hsupp form) =
      Open.SmoothOpenManifoldForm.supportedExtensionTo U W f (hf.mono h) hsupp
        (Open.SmoothOpenManifoldForm.restrict (inf_le_inf_left U h) form) := by
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  rw [Open.SmoothOpenManifoldForm.restrict_apply]
  by_cases hx : (x : M) ∈ U
  · rw [Open.SmoothOpenManifoldForm.supportedExtensionTo_apply_mem U V f hf hsupp form ⟨x, h x.property⟩ hx,
      Open.SmoothOpenManifoldForm.supportedExtensionTo_apply_mem U W f (hf.mono h) hsupp
        (Open.SmoothOpenManifoldForm.restrict (inf_le_inf_left U h) form) x hx, Open.SmoothOpenManifoldForm.restrict_apply]
  · have hnot : (x : M) ∉ tsupport f := fun hs => hx (hsupp hs)
    rw [Open.SmoothOpenManifoldForm.supportedExtensionTo_eq_zero_of_notMem_tsupport U V f hf hsupp form
        ⟨x, h x.property⟩ hnot,
      Open.SmoothOpenManifoldForm.supportedExtensionTo_eq_zero_of_notMem_tsupport U W f (hf.mono h) hsupp
        (Open.SmoothOpenManifoldForm.restrict (inf_le_inf_left U h) form) x hnot]

end

end OAI.Analysis.DifferentialForms.Manifold
