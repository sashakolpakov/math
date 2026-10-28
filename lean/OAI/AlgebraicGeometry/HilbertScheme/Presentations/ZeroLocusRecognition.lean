import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SectionZeroLocus

/-! # Zero Locus Recognition -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ZeroLocusRecognition

noncomputable section

/-! Recognizing a morphism as the closed zero locus of given global sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem isClosedImmersion_of_section_zero_universal
    {S : Scheme.{u}} {V M : Over S} (f : V ⟶ M) [Mono f]
    {ι : Type u} (s : ι → Γ(M.left, ⊤))
    (hf : ∀ i, f.left.appTop (s i) = 0)
    (hfactor : ∀ (T : Over S) (x : T ⟶ M),
      (∀ i, x.left.appTop (s i) = 0) → ∃ v : T ⟶ V, v ≫ f = x) :
    IsClosedImmersion f.left := by
  obtain ⟨Z, j, hj, eZ, heZ⟩ := SectionZeroLocus.section_zero_locus_representable M s
  let t : yoneda.obj V ⟶ (SectionZeroLocus.sectionZeroSubfunctor M s).toFunctor :=
    { app := fun _T => ↾fun v => ⟨v ≫ f, by
        intro i
        change v.left.appTop (f.left.appTop (s i)) = 0
        rw [hf i, map_zero]⟩
      naturality := by
        intro T U a
        apply ConcreteCategory.hom_ext
        intro v
        exact Subtype.ext (Category.assoc _ _ _) }
  have : IsIso t := by
    apply (NatTrans.isIso_iff_isIso_app t).mpr
    intro T
    apply (isIso_iff_bijective (t.app T)).mpr
    constructor
    · intro v w h
      apply (cancel_mono f).mp
      exact congrArg Subtype.val h
    · intro x
      obtain ⟨v, hv⟩ := hfactor T.unop x.val x.property
      exact ⟨v, Subtype.ext hv⟩
  let e : V ≅ Z := yoneda.preimageIso (asIso t ≪≫ eZ.symm)
  have he : yoneda.map e.hom ≫ eZ.hom = t := by
    simp [e]
  have hfac : e.hom ≫ j = f := by
    apply yoneda.map_injective
    rw [Functor.map_comp, ← heZ, ← Category.assoc, he]
    rfl
  have : IsClosedImmersion j.left := hj
  have : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
  have hc : IsClosedImmersion (e.hom.left ≫ j.left) := inferInstance
  exact (congrArg (fun g : V ⟶ M => g.left) hfac) ▸ hc

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ZeroLocusRecognition
