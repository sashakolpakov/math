import OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech
import OAI.Analysis.DifferentialForms.Manifold.GlobalOpen

/-! # Smooth Cech Augmentation -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechAugmentation

noncomputable section

/-!
# The degree-zero augmentation of the actual smooth Čech complex

The zero cocycles are exactly the compatible families of smooth forms.
The proved smooth gluing operation therefore identifies them with sections
on the union of the cover. This is the actual restriction augmentation;
no acyclicity or comparison theorem is assumed.
-/

open _root_.TopologicalSpace
open scoped BigOperators

universe u

variable {E ι : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (U : ι → Opens E) (p : ℕ)

omit [NormedSpace ℝ E] in
/-- A singleton Čech intersection is the indicated member of the open family. -/
theorem cechIntersection_singleton (a : Fin 1 → ι) :
    SmoothCech.cechIntersection U a = U (a 0) := by
  apply le_antisymm
  · exact SmoothCech.cechIntersection_le U a 0
  · apply le_iInf
    intro k
    have hk : k = 0 := Fin.eq_zero k
    subst k
    exact le_refl _

/-- Read a degree-zero Čech cochain as the usual family of local sections. -/
def smoothCechZeroFamily : SmoothCech.SmoothCechCochain U p 0 →ₗ[ℂ]
    ((i : ι) → Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (U i) p) where
  toFun c i := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict
    (le_of_eq (cechIntersection_singleton U (fun _ => i)).symm) (c (fun _ => i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Recover the cochain section from its local-section family. -/
theorem smoothCechZeroFamily_restrict (c : SmoothCech.SmoothCechCochain U p 0)
    (a : Fin 1 → ι) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (SmoothCech.cechIntersection_le U a 0)
      (smoothCechZeroFamily U p c (a 0)) = c a := by
  obtain ⟨i, rfl⟩ : ∃ i : ι, a = (fun _ : Fin 1 => i) :=
    ⟨a 0, funext (fun k => congrArg a (Fin.eq_zero k))⟩
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  rfl

/-- The local-section presentation loses no degree-zero information. -/
theorem smoothCechZeroFamily_injective :
    Function.Injective (smoothCechZeroFamily U p) := by
  intro c d h
  funext a
  rw [← smoothCechZeroFamily_restrict U p c a,
    ← smoothCechZeroFamily_restrict U p d a, h]

/-- In degree zero the Čech differential is the difference on the overlap. -/
theorem smoothCechDelta_zero_apply (c : SmoothCech.SmoothCechCochain U p 0)
    (a : Fin 2 → ι) :
    SmoothCech.smoothCechDelta U p 0 c a =
      Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (SmoothCech.cechIntersection_le U a 1)
        (smoothCechZeroFamily U p c (a 1)) -
      Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (SmoothCech.cechIntersection_le U a 0)
        (smoothCechZeroFamily U p c (a 0)) := by
  change ((b : Fin 1 → ι) → Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (SmoothCech.cechIntersection U b) p) at c
  erw [SmoothCech.smoothCechDelta_apply]
  change (∑ j : Fin 2, (-1 : ℤ) ^ j.val •
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (SmoothCech.cechIntersection_le_precomp U a j.succAbove)
      (c (a ∘ j.succAbove))) = _
  simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, Fin.val_one, pow_one]
  rw [← smoothCechZeroFamily_restrict U p c (a ∘ (0 : Fin 2).succAbove),
    ← smoothCechZeroFamily_restrict U p c (a ∘ (1 : Fin 2).succAbove)]
  rw [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_trans, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_trans]
  let s : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (SmoothCech.cechIntersection U a) p :=
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (SmoothCech.cechIntersection_le U a 1) (smoothCechZeroFamily U p c (a 1))
  let t : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (SmoothCech.cechIntersection U a) p :=
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (SmoothCech.cechIntersection_le U a 0) (smoothCechZeroFamily U p c (a 0))
  change (1 : ℤ) • s + (-1 : ℤ) • t = s - t
  exact (congrArg₂ (fun x y : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (SmoothCech.cechIntersection U a) p => x + y)
    (one_smul ℤ s) (neg_one_smul ℤ t)).trans (sub_eq_add_neg s t).symm

/-- Zero Čech cocycles are exactly compatible smooth local sections. -/
theorem smoothCechDelta_zero_iff_compatible (c : SmoothCech.SmoothCechCochain U p 0) :
    SmoothCech.smoothCechDelta U p 0 c = 0 ↔
      Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.Compatible (smoothCechZeroFamily U p c) := by
  constructor
  · intro hc i j x hi hj
    let a : Fin 2 → ι := ![i, j]
    have hx : x ∈ SmoothCech.cechIntersection U a := by
      apply (SmoothCech.mem_cechIntersection U a x).2
      exact Fin.forall_fin_two.2 ⟨hi, hj⟩
    have heq := congrFun hc a
    rw [smoothCechDelta_zero_apply] at heq
    have hs := sub_eq_zero.mp heq
    exact (congrArg (fun f : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (SmoothCech.cechIntersection U a) p => f ⟨x, hx⟩)
      hs).symm
  · intro hc
    funext a
    rw [smoothCechDelta_zero_apply]
    apply sub_eq_zero.mpr
    apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
    intro x
    exact hc (a 1) (a 0) x (SmoothCech.cechIntersection_le U a 1 x.property)
      (SmoothCech.cechIntersection_le U a 0 x.property)

variable (W : Opens E) (hsub : ∀ i, U i ≤ W)

/-- The augmentation is the actual restriction of a section to cover members. -/
def smoothCechAugmentation : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm W p →ₗ[ℂ] SmoothCech.SmoothCechCochain U p 0 where
  toFun form a := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict
    ((SmoothCech.cechIntersection_le U a 0).trans (hsub (a 0))) form
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The augmentation reads as the expected family of ordinary restrictions. -/
theorem smoothCechZeroFamily_augmentation (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm W p) (i : ι) :
    smoothCechZeroFamily U p (smoothCechAugmentation U p W hsub form) i =
      Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (hsub i) form := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  rfl

/-- Restrictions of a single section form a zero cocycle. -/
theorem smoothCechDelta_augmentation (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm W p) :
    SmoothCech.smoothCechDelta U p 0 (smoothCechAugmentation U p W hsub form) = 0 := by
  apply (smoothCechDelta_zero_iff_compatible U p _).2
  intro i j x hi hj
  rw [smoothCechZeroFamily_augmentation, smoothCechZeroFamily_augmentation]
  rfl

/-- The restriction augmentation with its codomain restricted to zero cocycles. -/
def smoothCechAugmentationToCycles :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm W p →ₗ[ℂ] LinearMap.ker (SmoothCech.smoothCechDelta U p 0) :=
  (smoothCechAugmentation U p W hsub).codRestrict _
    (fun form => smoothCechDelta_augmentation U p W hsub form)

variable (hcover : (W : Set E) ⊆ ⋃ i, (U i : Set E))

include hcover

/-- Restricting along a genuine cover is injective. -/
theorem smoothCechAugmentation_injective :
    Function.Injective (smoothCechAugmentation U p W hsub) := by
  intro form other h
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover x.property)
  have hr := congrArg (fun c => smoothCechZeroFamily U p c i) h
  rw [smoothCechZeroFamily_augmentation, smoothCechZeroFamily_augmentation] at hr
  exact congrArg (fun f : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (U i) p => f ⟨x, hi⟩) hr

/-- Smooth sheaf gluing proves every zero cocycle is the restriction of a section. -/
theorem smoothCechAugmentationToCycles_surjective :
    Function.Surjective (smoothCechAugmentationToCycles U p W hsub) := by
  intro c
  let family := smoothCechZeroFamily U p c.val
  have hc : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.Compatible family :=
    (smoothCechDelta_zero_iff_compatible U p c.val).1 c.property
  refine ⟨Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.glue hsub hcover family hc, ?_⟩
  apply Subtype.ext
  apply smoothCechZeroFamily_injective U p
  funext i
  change smoothCechZeroFamily U p
    (smoothCechAugmentation U p W hsub (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.glue hsub hcover family hc)) i = _
  rw [smoothCechZeroFamily_augmentation, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict_glue]

/-- Sections on the covered open set are linearly equivalent to zero Čech cocycles. -/
def smoothCechSectionsEquivCycles :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm W p ≃ₗ[ℂ] LinearMap.ker (SmoothCech.smoothCechDelta U p 0) :=
  LinearEquiv.ofBijective (smoothCechAugmentationToCycles U p W hsub)
    ⟨fun _form _other h => smoothCechAugmentation_injective U p W hsub hcover
      (congrArg Subtype.val h),
      smoothCechAugmentationToCycles_surjective U p W hsub hcover⟩

@[simp]
theorem smoothCechSectionsEquivCycles_apply (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm W p) :
    (smoothCechSectionsEquivCycles U p W hsub hcover form).val =
      smoothCechAugmentation U p W hsub form := rfl

/-- Exactness at the first Čech term uses the proved, genuine smooth gluing theorem. -/
theorem smoothCechAugmentation_range :
    LinearMap.range (smoothCechAugmentation U p W hsub) =
      LinearMap.ker (SmoothCech.smoothCechDelta U p 0) := by
  apply le_antisymm
  · rintro c ⟨form, rfl⟩
    exact smoothCechDelta_augmentation U p W hsub form
  · intro c hc
    obtain ⟨form, hform⟩ := smoothCechAugmentationToCycles_surjective
      U p W hsub hcover ⟨c, hc⟩
    exact ⟨form, congrArg Subtype.val hform⟩

omit hcover in
/-- For a cover of the entire space, zero Čech cocycles are genuine global smooth forms. -/
def smoothCechGlobalEquivCycles (hU : ∀ x : E, ∃ i, x ∈ U i) :
    Analysis.DifferentialForms.Manifold.Basic.SmoothForm E p ≃ₗ[ℂ] LinearMap.ker (SmoothCech.smoothCechDelta U p 0) :=
  Analysis.DifferentialForms.Manifold.Basic.SmoothForm.onTopEquiv.trans
    (smoothCechSectionsEquivCycles U p ⊤ (fun _ => le_top) (fun x _ =>
      Set.mem_iUnion.mpr (hU x)))

omit hcover in
/-- The global equivalence is the ordinary restriction map on every cover member. -/
theorem smoothCechGlobalEquivCycles_apply (hU : ∀ x : E, ∃ i, x ∈ U i)
    (form : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E p) (a : Fin 1 → ι) :
    (smoothCechGlobalEquivCycles U p hU form).val a =
      Analysis.DifferentialForms.Manifold.Basic.SmoothForm.onOpen (SmoothCech.cechIntersection U a) form := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  rfl

end

end OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechAugmentation
