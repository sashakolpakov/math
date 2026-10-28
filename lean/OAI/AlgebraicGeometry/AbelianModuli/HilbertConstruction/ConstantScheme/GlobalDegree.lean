import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Degree

/-! # Global Degree -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.GlobalDegree

noncomputable section

/-! Finite constant schemes have the expected rank over every base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u

theorem constantScheme_finrank {S : Scheme.{u}} (I : Type u) [Fintype I] (s : S) :
    (Iff.constantScheme S I).hom.finrank s = Fintype.card I := by
  let K := S.residueField s
  let a : Spec (.of K) ⟶ S := S.fromSpecResidueField s
  let k : Spec (.of K) := Classical.choice inferInstance
  let e := Constant.BaseChange.constantSchemeBaseChangeIso a I
  have : IsIso e.hom.left := inferInstanceAs (IsIso (((Over.forget (Spec (.of K))).mapIso e).hom))
  have h₁ : (Iff.constantScheme (Spec (.of K)) I).hom.finrank k =
      (pullback.snd (Iff.constantScheme S I).hom a).finrank k :=
    (congrArg (fun f : (Iff.constantScheme (Spec (.of K)) I).left ⟶ Spec (.of K) => f.finrank k)
      e.hom.w.symm).trans
      (congrFun (Scheme.Hom.finrank_comp_left_of_isIso e.hom.left
        (pullback.snd (Iff.constantScheme S I).hom a)) k)
  have h₂ : (pullback.snd (Iff.constantScheme S I).hom a).finrank k =
      (Iff.constantScheme S I).hom.finrank s :=
    (Scheme.Hom.finrank_pullback_snd (Iff.constantScheme S I).hom a k).trans
      (congrArg (Iff.constantScheme S I).hom.finrank (S.fromSpecResidueField_apply s k))
  exact (h₁.trans h₂).symm.trans (Degree.constantScheme_spec_finrank K I k)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.GlobalDegree
