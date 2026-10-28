import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.TorsorLabels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Translations

/-! # Self Pullback Translations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The split self-pullback is equivariant: translation in the second factor is right multiplication of the actual full-level labels. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {g N : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (level : A.FullLevel N)

def Abelian.Schemes.AbelianScheme.fullLevelSelfPullbackTranslation
    (a : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    Limits.pullback (A.multiplication N).left (A.multiplication N).left ⟶
      Limits.pullback (A.multiplication N).left (A.multiplication N).left :=
  Limits.pullback.lift (Limits.pullback.fst _ _)
    (Limits.pullback.snd _ _ ≫ (A.fullLevelMultiplicationTranslation level a).left)
    ((Limits.pullback.condition).trans
      ((congrArg (fun k => Limits.pullback.snd (A.multiplication N).left (A.multiplication N).left ≫ k)
        (A.fullLevelMultiplicationTranslation level a).w.symm).trans (Category.assoc _ _ _).symm))

theorem Abelian.Schemes.AbelianScheme.fullLevelSelfPullbackTranslation_fst
    (a : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    A.fullLevelSelfPullbackTranslation level a ≫ Limits.pullback.fst _ _ =
      Limits.pullback.fst (A.multiplication N).left (A.multiplication N).left :=
  Limits.pullback.lift_fst _ _ _

theorem Abelian.Schemes.AbelianScheme.fullLevelSelfPullbackTranslation_snd
    (a : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    A.fullLevelSelfPullbackTranslation level a ≫ Limits.pullback.snd _ _ =
      Limits.pullback.snd (A.multiplication N).left (A.multiplication N).left ≫
        (A.fullLevelMultiplicationTranslation level a).left :=
  Limits.pullback.lift_snd _ _ _

def Abelian.Schemes.AbelianScheme.fullLevelSelfPullbackLabel
    (i : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    A.scheme.left ⟶ Limits.pullback (A.multiplication N).left (A.multiplication N).left :=
  Limits.Sigma.ι (fun _ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) => A.scheme.left) i ≫
    (A.fullLevelSplitSelfPullbackIso level).hom

theorem Abelian.Schemes.AbelianScheme.fullLevelSelfPullbackLabel_fst
    (i : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    A.fullLevelSelfPullbackLabel level i ≫ Limits.pullback.fst _ _ = 𝟙 A.scheme.left :=
  (Category.assoc _ _ _).trans (A.fullLevelSplitSelfPullbackIso_label_fst level i)

theorem Abelian.Schemes.AbelianScheme.fullLevelSelfPullbackLabel_snd
    (i : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    A.fullLevelSelfPullbackLabel level i ≫ Limits.pullback.snd _ _ =
      (A.fullLevelMultiplicationTranslation level i).left :=
  (Category.assoc _ _ _).trans (A.fullLevelSplitSelfPullbackIso_label_snd level i)

theorem Abelian.Schemes.AbelianScheme.fullLevelSelfPullbackTranslation_label
    (a i : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    A.fullLevelSelfPullbackLabel level i ≫ A.fullLevelSelfPullbackTranslation level a =
      A.fullLevelSelfPullbackLabel level (i * a) := by
  apply Limits.pullback.hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => A.fullLevelSelfPullbackLabel level i ≫ k)
        (A.fullLevelSelfPullbackTranslation_fst level a)).trans
          ((A.fullLevelSelfPullbackLabel_fst level i).trans
            (A.fullLevelSelfPullbackLabel_fst level (i * a)).symm))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => A.fullLevelSelfPullbackLabel level i ≫ k)
        (A.fullLevelSelfPullbackTranslation_snd level a)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun k => k ≫ (A.fullLevelMultiplicationTranslation level a).left)
              (A.fullLevelSelfPullbackLabel_snd level i)).trans
                ((congrArg (fun k : Over.mk (A.multiplication N).left ⟶
                    Over.mk (A.multiplication N).left => k.left)
                  (A.fullLevelMultiplicationTranslation_comp level i a)).trans
                    (A.fullLevelSelfPullbackLabel_snd level (i * a)).symm))))

theorem Abelian.Schemes.AbelianScheme.fullLevelSplitSelfPullbackIso_equivariant
    (a : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    (ConstantScheme.Translations.constantSchemeRightTranslation A.scheme.left _ a).left ≫ (A.fullLevelSplitSelfPullbackIso level).hom =
      (A.fullLevelSplitSelfPullbackIso level).hom ≫ A.fullLevelSelfPullbackTranslation level a := by
  apply Limits.Sigma.hom_ext
  intro i
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (A.fullLevelSplitSelfPullbackIso level).hom)
      (ConstantScheme.Translations.constantSchemeRightTranslation_label A.scheme.left _ a i)).trans
        ((A.fullLevelSelfPullbackTranslation_label level a i).symm.trans (Category.assoc _ _ _)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
