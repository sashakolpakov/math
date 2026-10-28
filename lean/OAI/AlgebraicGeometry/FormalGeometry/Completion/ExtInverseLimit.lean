import OAI.AlgebraicGeometry.FormalGeometry.Completion.ExtensionTransition
import Mathlib.CategoryTheory.Functor.OfSequence

/-! # Ext Inverse Limit -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ExtInverseLimit.Construction

noncomputable section

/-!
# Completion: degree-one detection by an inverse system of coefficients

Surjectivity of transitions on degree-zero morphisms permits compatible
splittings of coefficient pushouts. Their differences reconstruct a
retraction through the coefficient limit, which kills the original Ext¹ class.
-/

open _root_.CategoryTheory Limits Abelian Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- An extension splits if its coefficient pushouts split and the coefficient
system has surjective degree-zero transitions. -/
theorem extClass_eq_zero_of_inverseLimit (S : ShortComplex C) (hS : S.ShortExact)
    (F : ℕᵒᵖ ⥤ C) (q : (Functor.const ℕᵒᵖ).obj S.X₁ ⟶ F)
    (hq : IsLimit (Cone.mk S.X₁ q))
    (hsurj : ∀ n, Function.Surjective
      (fun d : S.X₃ ⟶ F.obj (op (n + 1)) => d ≫ F.map (homOfLE (Nat.le_succ n)).op))
    (hvan : ∀ n, hS.extClass.comp (Ext.mk₀ (q.app (op n))) (add_zero 1) = 0) :
    hS.extClass = 0 := by
  let T (n : ℕ) := ExtPushout.Construction.pushoutExtensionComplex S (q.app (op n))
  have hT (n : ℕ) : (T n).ShortExact := ExtPushout.Construction.pushoutExtensionComplex_shortExact hS _
  have : ∀ n, Mono (T n).f := fun n => (hT n).mono_f
  let j (n : ℕ) : S.X₂ ⟶ (T n).X₂ := pushout.inl S.f (q.app (op n))
  have hjg (n : ℕ) : j n ≫ (T n).g = S.g := pushout.inl_desc _ _ _
  let r (n : ℕ) := F.map (homOfLE (Nat.le_succ n)).op
  have hqstep (n : ℕ) : q.app (op (n + 1)) ≫ r n = q.app (op n) := by
    simpa [r] using (q.naturality (homOfLE (Nat.le_succ n)).op).symm
  let e (n : ℕ) : (T (n + 1)).X₂ ⟶ (T n).X₂ :=
    ExtensionTransition.Construction.pushoutExtensionTransition S _ _ (r n) (hqstep n)
  have heg (n : ℕ) : e n ≫ (T n).g = (T (n + 1)).g :=
    ExtensionTransition.Construction.pushoutExtensionTransition_g S _ _ _ _
  have hje (n : ℕ) : j (n + 1) ≫ e n = j n := ExtensionTransition.Construction.pushoutExtensionTransition_inl S _ _ _ _
  let Spl (n : ℕ) := {s : S.X₃ ⟶ (T n).X₂ // s ≫ (T n).g = 𝟙 _}
  have hSpl (n : ℕ) : Nonempty (Spl n) := by
    obtain ⟨s, hs⟩ := (ExtPushout.Construction.extClass_coefficientMap_eq_zero_iff hS (q.app (op n))).mp (hvan n)
    exact ⟨s, hs⟩
  let step (n : ℕ) : Spl (n + 1) → Spl n := fun s =>
    ⟨s.val ≫ e n, by rw [Category.assoc, heg, s.property]⟩
  have hstep (n : ℕ) : Function.Surjective (step n) := by
    intro s
    let t := Classical.choice (hSpl (n + 1))
    obtain ⟨t', ht', hts⟩ := ExtensionTransition.Construction.exists_compatible_pushout_section S _ _ (r n) (hqstep n)
      hS (hsurj n) t.val t.property s.val s.property
    exact ⟨⟨t', ht'⟩, Subtype.ext hts⟩
  let s : ∀ n, Spl n := fun n => Nat.rec (Classical.choice (hSpl 0))
    (fun n s => (hstep n s).choose) n
  have hs (n : ℕ) : (s (n + 1)).val ≫ e n = (s n).val :=
    congrArg Subtype.val (hstep n (s n)).choose_spec
  let d (n : ℕ) : S.X₂ ⟶ (T n).X₂ :=
    j n - S.g ≫ (s n).val
  have hd (n : ℕ) : d n ≫ (T n).g = 0 := by
    simp only [d, Preadditive.sub_comp, hjg, Category.assoc, (s n).property,
      Category.comp_id, sub_self]
  let ρ (n : ℕ) : S.X₂ ⟶ F.obj (op n) :=
    (KernelFork.IsLimit.lift' (hT n).exact.fIsKernel (d n) (hd n)).val
  have hρ (n : ℕ) : ρ n ≫ (T n).f = d n :=
    (KernelFork.IsLimit.lift' (hT n).exact.fIsKernel (d n) (hd n)).property
  have hρstep (n : ℕ) : ρ (n + 1) ≫ r n = ρ n := by
    have : Mono (T n).f := (hT n).mono_f
    apply (cancel_mono (T n).f).mp
    rw [Category.assoc]
    change ρ (n + 1) ≫ r n ≫ pushout.inr S.f (q.app (op n)) = _
    rw [← ExtensionTransition.Construction.pushoutExtensionTransition_inr S _ _ (r n) (hqstep n), ← Category.assoc]
    change (ρ (n + 1) ≫ (T (n + 1)).f) ≫ e n = ρ n ≫ (T n).f
    rw [hρ, hρ]
    simp only [d, Preadditive.sub_comp, Category.assoc, hs, hje]
  let ρcone : Cone F := ⟨S.X₂, NatTrans.ofOpSequence ρ (by
    intro n
    simpa [r] using (hρstep n).symm)⟩
  let ret := hq.lift ρcone
  have hret (n : ℕ) : ret ≫ q.app (op n) = ρ n := hq.fac ρcone (op n)
  apply ExtensionTransition.Construction.extClass_eq_zero_of_retraction S hS ret
  apply hq.hom_ext
  intro n
  change (S.f ≫ ret) ≫ q.app n = (𝟙 S.X₁) ≫ q.app n
  rw [Category.assoc, hret n.unop, Category.id_comp]
  have : Mono (T n.unop).f := (hT n.unop).mono_f
  apply (cancel_mono (T n.unop).f).mp
  rw [Category.assoc, hρ]
  simp only [d, Preadditive.comp_sub, ← Category.assoc, S.zero, zero_comp, sub_zero]
  exact pushout.condition

/-- Actual Ext¹ classes are detected by this inverse system of coefficients. -/
theorem ext_one_eq_zero_of_inverseLimit [EnoughInjectives C]
    (F : ℕᵒᵖ ⥤ C) (c : Cone F) (hc : IsLimit c) (X : C)
    (hsurj : ∀ n, Function.Surjective
      (fun d : X ⟶ F.obj (op (n + 1)) => d ≫ F.map (homOfLE (Nat.le_succ n)).op))
    (x : Ext X c.pt 1)
    (hx : ∀ n, x.comp (Ext.mk₀ (c.π.app (op n))) (add_zero 1) = 0) : x = 0 := by
  obtain ⟨E, i, p, h, hS, he⟩ := ExtExtensions.Construction.ext_one_exists_shortExact x
  rw [← he]
  exact extClass_eq_zero_of_inverseLimit (ShortComplex.mk i p h) hS F c.π hc hsurj
    (fun n => he ▸ hx n)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ExtInverseLimit.Construction
