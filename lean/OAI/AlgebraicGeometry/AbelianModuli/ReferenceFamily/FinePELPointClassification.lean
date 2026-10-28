import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Classifying

/-! # Fine PEL Point Classification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

section

/-! The original fine PEL model classifies all actual PEL isomorphism
classes on each test scheme, without choosing a marking or an atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine)

include hM in
theorem Models.FinePELModel.familyClassifying_bijective (T : Over (Spec (.of K))) :
    Function.Bijective (fun f : T ⟶ M.space => (M.universal.pullback f).classOf) := by
  constructor
  · intro f g h
    obtain ⟨j, _, hu⟩ := hM T (M.universal.pullback f)
    have hf : Nonempty (Models.PELPullbackIso M.universal (M.universal.pullback f) f) :=
      ⟨Models.PELPullbackIso.ofPELIso (PEL.Objects.PELIso.refl _)⟩
    have hg : Nonempty (Models.PELPullbackIso M.universal (M.universal.pullback f) g) :=
      (Models.PELPullbackIso.nonempty_iff_classOf g).mpr h
    exact (hu f hf).trans (hu g hg).symm
  · intro q
    induction q using Quotient.inductionOn with
    | h A =>
      obtain ⟨f, ⟨e⟩, _⟩ := hM T A
      exact ⟨f, Quotient.sound ⟨e.toPELIso.symm⟩⟩

def Models.FinePELModel.familyClassifyingEquiv (T : Over (Spec (.of K))) : (T ⟶ M.space) ≃ PEL.Objects.PELClasses P iota N T :=
  Equiv.ofBijective (fun f => (M.universal.pullback f).classOf) (M.familyClassifying_bijective hM T)

end

/-! Genuine complex points of the model's native base change are exactly
its PEL families over the specified complex embedding of the base field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (κ : K →+* ℂ)

def Models.FinePELModel.complexPointBaseEquiv : M.ComplexPoints κ ≃
    (Over.mk (Spec.map (CommRingCat.ofHom κ)) ⟶ M.space) where
  toFun x := Over.homMk (x.left ≫ pullback.fst M.space.hom (Spec.map (CommRingCat.ofHom κ))) (by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => x.left ≫ z) (pullback.condition (f := M.space.hom)
        (g := Spec.map (CommRingCat.ofHom κ)))).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun z => z ≫ Spec.map (CommRingCat.ofHom κ)) x.w).trans (Category.id_comp _)))))
  invFun f := Over.homMk
    (pullback.lift f.left (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) (f.w.trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _)
  left_inv x := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans x.w.symm
  right_inv f := Over.OverMorphism.ext (pullback.lift_fst _ _ _)

def Models.FinePELModel.complexPointClassEquiv (hM : M.IsFine) : M.ComplexPoints κ ≃
    PEL.Objects.PELClasses P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ))) :=
  (M.complexPointBaseEquiv κ).trans (M.familyClassifyingEquiv hM _)

theorem Models.FinePELModel.complexPointClassEquiv_apply (hM : M.IsFine) (x : M.ComplexPoints κ) :
    M.complexPointClassEquiv κ hM x = (M.universal.pullback (M.complexPointBaseEquiv κ x)).classOf := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
