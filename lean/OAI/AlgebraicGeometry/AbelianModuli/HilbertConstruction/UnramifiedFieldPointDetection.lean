import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Unramified Field Point Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedFieldPointDetection

noncomputable section

/-! Morphisms into an unramified relative scheme are determined by their composites with all residue-field points, without any reducedness assumption on the source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem unramified_hom_eq_of_residueFieldPoints {X T S : Scheme.{u}}
    (p : X ⟶ S) [LocallyOfFiniteType p] [FormallyUnramified p]
    (f g : T ⟶ X) (hbase : f ≫ p = g ≫ p)
    (h : ∀ x : T, T.fromSpecResidueField x ≫ f = T.fromSpecResidueField x ≫ g) : f = g := by
  let d := pullback.lift f g hbase
  let δ := pullback.diagonal p
  have : IsOpenImmersion δ := inferInstance
  have hr : Set.range d ⊆ Set.range δ := by
    rintro _ ⟨x, rfl⟩
    let s := T.fromSpecResidueField x
    have H : s ≫ d = (s ≫ f) ≫ δ := by
      apply pullback.hom_ext
      · simp only [Category.assoc, d, δ, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
      · simpa only [Category.assoc, d, δ, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id] using (h x).symm
    obtain ⟨z⟩ := (inferInstance : Nonempty (Spec (T.residueField x)))
    refine ⟨f x, ?_⟩
    have Hx := congrArg (fun v : Spec (T.residueField x) ⟶ pullback p p => v z) H
    change d (T.fromSpecResidueField x z) = δ (f (T.fromSpecResidueField x z)) at Hx
    simpa only [Scheme.fromSpecResidueField_apply] using Hx.symm
  let a := IsOpenImmersion.lift δ d hr
  have ha : a ≫ δ = d := IsOpenImmersion.lift_fac δ d hr
  have hf : a = f := by
    have H := congrArg (fun v => v ≫ pullback.fst p p) ha
    simpa only [Category.assoc, δ, d, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst] using H
  have hg : a = g := by
    have H := congrArg (fun v => v ≫ pullback.snd p p) ha
    simpa only [Category.assoc, δ, d, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd] using H
  exact hf.symm.trans hg

theorem unramified_overHom_eq_of_fieldPoints {S : Scheme.{u}} {T M : Over S}
    [LocallyOfFiniteType M.hom] [FormallyUnramified M.hom] (a b : T ⟶ M)
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ T.left), s ≫ a.left = s ≫ b.left) : a = b := by
  apply Over.OverMorphism.ext
  apply unramified_hom_eq_of_residueFieldPoints M.hom a.left b.left (a.w.trans b.w.symm)
  intro x
  exact h (T.left.residueField x) (T.left.fromSpecResidueField x)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedFieldPointDetection
