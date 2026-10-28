import OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenTangent
import OAI.Analysis.DifferentialForms.Manifold.LocalPullback
import OAI.Analysis.DifferentialForms.Manifold.OpenDerivative

/-! # Intrinsic Open Equivalence -/

namespace OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence

noncomputable section

/-!
# Actual forms on an open domain and its intrinsic manifold

Ambient local forms are transported through the actual derivative of open
inclusion. The local inverse proves both the inverse law and preservation of
smoothness. The resulting equivalence intertwines genuine exterior
derivatives and commutes with further open restriction.
-/

open Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {U V : Opens M} {n : ℕ}

/-- Pullback of an ambient local smooth field is intrinsically smooth. -/
theorem intrinsicOpenRawEquiv_smooth (form : Open.RawOpenManifoldForm E U n)
    (hform : Algebra.IsSmoothManifoldFormOn (Open.openManifoldFormExtension U form) (U : Set M)) :
    Algebra.IsSmoothManifoldFormOn (IntrinsicOpenTangent.intrinsicOpenRawEquiv U n form) univ := by
  rw [IntrinsicOpenTangent.intrinsicOpenRawEquiv_eq_pullback]
  exact Algebra.RawManifoldForm.pullback_smooth_on (Open.openManifoldFormExtension U form)
    isOpen_univ U.isOpen hform (Subtype.val : U → M)
    (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞)).contMDiffOn
    (fun x _ => x.property)

/-- Inverse tangent transport of an intrinsic smooth field is smooth on the ambient open. -/
theorem intrinsicOpenRawEquiv_symm_smooth (form : Algebra.RawManifoldForm E U n)
    (hform : Algebra.IsSmoothManifoldFormOn form univ) :
    Algebra.IsSmoothManifoldFormOn
      (Open.openManifoldFormExtension U ((IntrinsicOpenTangent.intrinsicOpenRawEquiv U n).symm form)) (U : Set M) := by
  intro e he y hy
  let hs : Nonempty U := ⟨⟨e.symm y, hy.2⟩⟩
  have hp : Algebra.IsSmoothManifoldFormOn
      (form.pullback (E := E) (U.openPartialHomeomorphSubtypeCoe hs).symm) (U : Set M) :=
    Algebra.RawManifoldForm.pullback_smooth_on form U.isOpen isOpen_univ hform
      (U.openPartialHomeomorphSubtypeCoe hs).symm
      (IntrinsicOpenTangent.intrinsicOpenInverse_contMDiffOn (E := E) hs) (fun _ _ => mem_univ _)
  exact (hp.congr (fun x hx => (IntrinsicOpenTangent.intrinsicOpenRawEquiv_symm_extension hs form hx).symm)) e he y hy

/-- The two actual smoothness conditions coincide under inclusion tangent transport. -/
theorem intrinsicOpenRawEquiv_smooth_iff (form : Open.RawOpenManifoldForm E U n) :
    Algebra.IsSmoothManifoldFormOn (IntrinsicOpenTangent.intrinsicOpenRawEquiv U n form) univ ↔
      Algebra.IsSmoothManifoldFormOn (Open.openManifoldFormExtension U form) (U : Set M) := by
  constructor
  · intro hform
    simpa only [LinearEquiv.symm_apply_apply] using
      intrinsicOpenRawEquiv_symm_smooth (IntrinsicOpenTangent.intrinsicOpenRawEquiv U n form) hform
  · exact intrinsicOpenRawEquiv_smooth form

variable (E) in
/-- Ambient local forms and intrinsic open-manifold forms are canonically complex-linearly equivalent. -/
def intrinsicOpenFormEquiv (U : Opens M) (n : ℕ) :
    Open.SmoothOpenManifoldForm E U n ≃ₗ[ℂ] Algebra.SmoothManifoldForm E U n where
  toFun form := ⟨IntrinsicOpenTangent.intrinsicOpenRawEquiv U n (form : Open.RawOpenManifoldForm E U n),
    intrinsicOpenRawEquiv_smooth _ form.smooth⟩
  invFun form := ⟨(IntrinsicOpenTangent.intrinsicOpenRawEquiv U n).symm (form : Algebra.RawManifoldForm E U n),
    intrinsicOpenRawEquiv_symm_smooth _ form.smooth⟩
  left_inv form := Subtype.ext
    ((IntrinsicOpenTangent.intrinsicOpenRawEquiv U n).left_inv (form : Open.RawOpenManifoldForm E U n))
  right_inv form := Subtype.ext
    ((IntrinsicOpenTangent.intrinsicOpenRawEquiv U n).right_inv (form : Algebra.RawManifoldForm E U n))
  map_add' form other := Subtype.ext ((IntrinsicOpenTangent.intrinsicOpenRawEquiv U n).map_add
    (form : Open.RawOpenManifoldForm E U n) (other : Open.RawOpenManifoldForm E U n))
  map_smul' c form := Subtype.ext
    ((IntrinsicOpenTangent.intrinsicOpenRawEquiv U n).map_smul c (form : Open.RawOpenManifoldForm E U n))

@[simp]
theorem intrinsicOpenFormEquiv_apply (form : Open.SmoothOpenManifoldForm E U n) (x : U) :
    intrinsicOpenFormEquiv E U n form x =
      (form x).compContinuousLinearMap
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → M) x) := rfl

@[simp]
theorem intrinsicOpenFormEquiv_symm_apply (form : Algebra.SmoothManifoldForm E U n) (x : U) :
    (intrinsicOpenFormEquiv E U n).symm form x =
      (form x).compContinuousLinearMap
        (IntrinsicOpenTangent.intrinsicOpenTangentEquiv (E := E) x).symm.toContinuousLinearMap := rfl

/-- The identification preserves the two genuine exterior derivatives. -/
theorem intrinsicOpenFormEquiv_d (form : Open.SmoothOpenManifoldForm E U n) :
    Algebra.SmoothManifoldForm.d (intrinsicOpenFormEquiv E U n form) =
      intrinsicOpenFormEquiv E U (n + 1) (Open.SmoothOpenManifoldForm.d form) := by
  apply Algebra.SmoothManifoldForm.ext
  intro x
  change (IntrinsicOpenTangent.intrinsicOpenRawEquiv U n (form : Open.RawOpenManifoldForm E U n)).exteriorDerivative x =
    (Open.SmoothOpenManifoldForm.d form x).compContinuousLinearMap
      (IntrinsicOpenTangent.intrinsicOpenTangentEquiv (E := E) x).toContinuousLinearMap
  rw [IntrinsicOpenTangent.intrinsicOpenRawEquiv_eq_pullback, IntrinsicOpenTangent.intrinsicOpenTangentEquiv_coe]
  exact form.extension.exteriorDerivative_pullback_on isOpen_univ U.isOpen form.smooth
    (Subtype.val : U → M) (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞)).contMDiffOn
    (fun y _ => y.property) (mem_univ x)

theorem intrinsicOpenFormEquiv_symm_d (form : Algebra.SmoothManifoldForm E U n) :
    Open.SmoothOpenManifoldForm.d ((intrinsicOpenFormEquiv E U n).symm form) =
      (intrinsicOpenFormEquiv E U (n + 1)).symm (Algebra.SmoothManifoldForm.d form) := by
  apply (intrinsicOpenFormEquiv E U (n + 1)).injective
  rw [LinearEquiv.apply_symm_apply, ← intrinsicOpenFormEquiv_d, LinearEquiv.apply_symm_apply]

/-- For a global ambient form, the identification is exactly pullback by open inclusion. -/
theorem intrinsicOpenFormEquiv_onOpen (form : Algebra.SmoothManifoldForm E M n) :
    intrinsicOpenFormEquiv E U n (Algebra.SmoothManifoldForm.onOpen U form) =
      Algebra.SmoothManifoldForm.pullback (Subtype.val : U → M)
        (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞)) form := by
  apply Algebra.SmoothManifoldForm.ext
  intro x
  rw [intrinsicOpenFormEquiv_apply, Algebra.SmoothManifoldForm.pullback_apply]
  rfl

/-- Further ambient restriction corresponds to intrinsic pullback by the nested-open inclusion. -/
theorem intrinsicOpenFormEquiv_restrict (h : U ≤ V) (form : Open.SmoothOpenManifoldForm E V n) :
    intrinsicOpenFormEquiv E U n (Open.SmoothOpenManifoldForm.restrict h form) =
      Algebra.SmoothManifoldForm.pullback (Opens.inclusion h)
        (contMDiff_inclusion (I := 𝓘(ℝ, E)) (n := ∞) h)
        (intrinsicOpenFormEquiv E V n form) := by
  apply Algebra.SmoothManifoldForm.ext
  intro x
  rw [intrinsicOpenFormEquiv_apply, Algebra.SmoothManifoldForm.pullback_apply,
    intrinsicOpenFormEquiv_apply, Open.SmoothOpenManifoldForm.restrict_apply]
  have hchain : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → M) x =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : V → M) (Opens.inclusion h x)).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Opens.inclusion h) x) :=
    mfderiv_comp x
      ((contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := V) (n := ∞)).mdifferentiableAt (by simp))
      ((contMDiff_inclusion (I := 𝓘(ℝ, E)) (n := ∞) h).mdifferentiableAt (by simp))
  ext v
  change form ⟨(x : M), h x.property⟩
      (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → M) x (v i)) =
    form (Opens.inclusion h x)
      (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : V → M) (Opens.inclusion h x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Opens.inclusion h) x (v i)))
  apply congrArg (form ⟨(x : M), h x.property⟩)
  funext i
  exact congrArg (fun linear => linear (v i)) hchain

end

end OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence
