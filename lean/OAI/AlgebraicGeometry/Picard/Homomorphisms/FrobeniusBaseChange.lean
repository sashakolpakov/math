import OAI.AlgebraicGeometry.Picard.Homomorphisms.Group
import OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupDescent
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Frobenius Base Change -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusBaseChange

noncomputable section

/-! Relative Frobenius commutes with every change of the base scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable (p : ℕ) (hp : p.Prime) {S T : Scheme.{u}}
variable (hS : (p : Γ(S, ⊤)) = 0) (s : T ⟶ S) (A : Over S)

def frobeniusTwistBaseChangeSchemeIso :
    (Frobenius.Construction.frobeniusTwist p hp (Frobenius.Construction.prime_eq_zero_of_map p hS s) ((Over.pullback s).obj A)).left ≅
      ((Over.pullback s).obj (Frobenius.Construction.frobeniusTwist p hp hS A)).left :=
  pullbackLeftPullbackSndIso A.hom s
      (Frobenius.Construction.absoluteFrobenius p hp T (Frobenius.Construction.prime_eq_zero_of_map p hS s)) ≪≫
    pullback.congrHom rfl (Frobenius.Construction.absoluteFrobenius_naturality p hp _ hS s) ≪≫
      (pullbackLeftPullbackSndIso A.hom (Frobenius.Construction.absoluteFrobenius p hp S hS) s).symm

@[reassoc (attr := simp)]
theorem frobeniusTwistBaseChangeSchemeIso_hom_snd :
    (frobeniusTwistBaseChangeSchemeIso p hp hS s A).hom ≫
      pullback.snd (Frobenius.Construction.frobeniusTwist p hp hS A).hom s =
        (Frobenius.Construction.frobeniusTwist p hp (Frobenius.Construction.prime_eq_zero_of_map p hS s) ((Over.pullback s).obj A)).hom := by
  simp [frobeniusTwistBaseChangeSchemeIso, Frobenius.Construction.frobeniusTwist, pullback.map]
  erw [pullback.lift_snd, pullbackLeftPullbackSndIso_hom_snd]

@[reassoc (attr := simp)]
theorem frobeniusTwistBaseChangeSchemeIso_hom_fst_fst :
    (frobeniusTwistBaseChangeSchemeIso p hp hS s A).hom ≫
      pullback.fst (Frobenius.Construction.frobeniusTwist p hp hS A).hom s ≫
        pullback.fst A.hom (Frobenius.Construction.absoluteFrobenius p hp S hS) =
      pullback.fst ((Over.pullback s).obj A).hom
        (Frobenius.Construction.absoluteFrobenius p hp T (Frobenius.Construction.prime_eq_zero_of_map p hS s)) ≫
          pullback.fst A.hom s := by
  simp [frobeniusTwistBaseChangeSchemeIso, Frobenius.Construction.frobeniusTwist, pullback.map]
  erw [pullback.lift_fst, pullbackLeftPullbackSndIso_hom_fst]

def frobeniusTwistBaseChangeIso :
    Frobenius.Construction.frobeniusTwist p hp (Frobenius.Construction.prime_eq_zero_of_map p hS s) ((Over.pullback s).obj A) ≅
      (Over.pullback s).obj (Frobenius.Construction.frobeniusTwist p hp hS A) :=
  Over.isoMk (frobeniusTwistBaseChangeSchemeIso p hp hS s A)
    (frobeniusTwistBaseChangeSchemeIso_hom_snd p hp hS s A)

theorem relativeFrobenius_baseChange_left_fst_fst :
    (Frobenius.Construction.relativeFrobenius p hp (Frobenius.Construction.prime_eq_zero_of_map p hS s) ((Over.pullback s).obj A)).left ≫
      (frobeniusTwistBaseChangeSchemeIso p hp hS s A).hom ≫
        pullback.fst (Frobenius.Construction.frobeniusTwist p hp hS A).hom s ≫
          pullback.fst A.hom (Frobenius.Construction.absoluteFrobenius p hp S hS) =
      pullback.fst A.hom s ≫
        Frobenius.Construction.absoluteFrobenius p hp A.left (Frobenius.Construction.prime_eq_zero_of_map p hS A.hom) := by
  let X := (Over.pullback s).obj A
  let FX := (Frobenius.Construction.relativeFrobenius p hp (Frobenius.Construction.prime_eq_zero_of_map p hS s) X).left
  let r := pullback.fst X.hom (Frobenius.Construction.absoluteFrobenius p hp T (Frobenius.Construction.prime_eq_zero_of_map p hS s))
  let a := pullback.fst A.hom s
  have h₁ := congrArg (fun z => FX ≫ z)
    (frobeniusTwistBaseChangeSchemeIso_hom_fst_fst p hp hS s A)
  have h₂ := congrArg (fun z => z ≫ a)
    (Frobenius.Construction.relativeFrobenius_comp_fst p hp (Frobenius.Construction.prime_eq_zero_of_map p hS s) X)
  exact h₁.trans ((Category.assoc FX r a).symm.trans
    (h₂.trans (Frobenius.Construction.absoluteFrobenius_naturality p hp _ _ a)))

theorem relativeFrobenius_baseChange_right_fst_fst :
    ((Over.pullback s).map (Frobenius.Construction.relativeFrobenius p hp hS A)).left ≫
      pullback.fst (Frobenius.Construction.frobeniusTwist p hp hS A).hom s ≫
        pullback.fst A.hom (Frobenius.Construction.absoluteFrobenius p hp S hS) =
      pullback.fst A.hom s ≫
        Frobenius.Construction.absoluteFrobenius p hp A.left (Frobenius.Construction.prime_eq_zero_of_map p hS A.hom) := by
  let F := Frobenius.Construction.relativeFrobenius p hp hS A
  have h : ((Over.pullback s).map F).left ≫
      pullback.fst (Frobenius.Construction.frobeniusTwist p hp hS A).hom s = pullback.fst A.hom s ≫ F.left :=
    pullback.lift_fst _ _ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ pullback.fst A.hom (Frobenius.Construction.absoluteFrobenius p hp S hS)) h).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun z => pullback.fst A.hom s ≫ z)
          (Frobenius.Construction.relativeFrobenius_comp_fst p hp hS A))))

theorem relativeFrobenius_baseChange :
    Frobenius.Construction.relativeFrobenius p hp (Frobenius.Construction.prime_eq_zero_of_map p hS s) ((Over.pullback s).obj A) ≫
      (frobeniusTwistBaseChangeIso p hp hS s A).hom =
        (Over.pullback s).map (Frobenius.Construction.relativeFrobenius p hp hS A) := by
  let l := Frobenius.Construction.relativeFrobenius p hp (Frobenius.Construction.prime_eq_zero_of_map p hS s) ((Over.pullback s).obj A) ≫
    (frobeniusTwistBaseChangeIso p hp hS s A).hom
  let r := (Over.pullback s).map (Frobenius.Construction.relativeFrobenius p hp hS A)
  have hsnd : l.left ≫ pullback.snd (Frobenius.Construction.frobeniusTwist p hp hS A).hom s =
      r.left ≫ pullback.snd (Frobenius.Construction.frobeniusTwist p hp hS A).hom s := l.w.trans r.w.symm
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · have h := (relativeFrobenius_baseChange_left_fst_fst p hp hS s A).trans
        (relativeFrobenius_baseChange_right_fst_fst p hp hS s A).symm
      let a := (Frobenius.Construction.relativeFrobenius p hp (Frobenius.Construction.prime_eq_zero_of_map p hS s)
        ((Over.pullback s).obj A)).left
      let b := (frobeniusTwistBaseChangeSchemeIso p hp hS s A).hom
      let c := pullback.fst (Frobenius.Construction.frobeniusTwist p hp hS A).hom s
      let d := pullback.fst A.hom (Frobenius.Construction.absoluteFrobenius p hp S hS)
      exact (Category.assoc (a ≫ b) c d).trans
        ((Category.assoc a b (c ≫ d)).trans (h.trans (Category.assoc r.left c d).symm))
    · have hl := congrArg (fun z => l.left ≫ z)
        (pullback.condition (f := (Frobenius.Construction.frobeniusTwist p hp hS A).hom) (g := s))
      have hr := congrArg (fun z => r.left ≫ z)
        (pullback.condition (f := (Frobenius.Construction.frobeniusTwist p hp hS A).hom) (g := s))
      have he := congrArg (fun z => z ≫ s) hsnd
      exact (Category.assoc _ _ _).trans (hl.trans
        ((Category.assoc _ _ _).symm.trans (he.trans
          ((Category.assoc _ _ _).trans (hr.symm.trans (Category.assoc _ _ _).symm)))))
  · exact hsnd

instance frobeniusTwistBaseChangeIso_isMonHom [GrpObj A] [Smooth A.hom] :
    IsMonHom (frobeniusTwistBaseChangeIso p hp hS s A).hom := by
  let X := (Over.pullback s).obj A
  let F := Frobenius.Construction.relativeFrobenius p hp (Frobenius.Construction.prime_eq_zero_of_map p hS s) X
  have : Smooth X.hom := inferInstanceAs (Smooth (pullback.snd A.hom s))
  have : Flat F.left := Homomorphisms.Smooth.Construction.relativeFrobenius_smooth_flat p hp _ X
  have : EffectiveEpi (F ⊗ₘ F) := GroupDescent.Construction.effectiveEpi_tensor_over_of_fpqc F F
  exact GroupDescent.Construction.descended_isMonHom F ((Over.pullback s).map (Frobenius.Construction.relativeFrobenius p hp hS A))
    (frobeniusTwistBaseChangeIso p hp hS s A).hom
    (relativeFrobenius_baseChange p hp hS s A)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusBaseChange
