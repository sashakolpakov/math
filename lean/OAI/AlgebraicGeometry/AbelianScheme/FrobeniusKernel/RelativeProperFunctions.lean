import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineFaithfulness
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Kernel

/-! # Relative Proper Functions -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RelativeProperFunctions.Construction

noncomputable section

/-! Proper-group functions remain constant along the group coordinate
after an arbitrary affine parameter change and a further affine test. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineFaithfulness.Construction.KernelCharacters

variable {k : Type u} [Field k]
variable (A : Over (Spec (.of k))) [GrpObj A]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

theorem properGroup_iteratedParameter_appTop_isIso (Q : Over (Spec (.of k)))
    (V : Over Q.left) [IsAffine V.left] :
    IsIso (fst V ((Over.pullback Q.hom).obj A)).left.appTop := by
  let e := (Over.pullbackComp V.hom Q.hom).app A
  have : IsAffine ((Over.map Q.hom).obj V).left := inferInstanceAs (IsAffine V.left)
  have hs : IsIso ((Over.pullback (V.hom ≫ Q.hom)).obj A).hom.appTop :=
    CartierDuality.CharacterLineFaithfulness.Construction.KernelCharacters.properGroup_parameter_appTop_isIso A ((Over.map Q.hom).obj V)
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget V.left).map e.inv))
  have : IsIso e.inv.left.appTop :=
    inferInstanceAs (IsIso (Scheme.Γ.map e.inv.left.op))
  have he : e.inv.left ≫ ((Over.pullback (V.hom ≫ Q.hom)).obj A).hom =
      ((Over.pullback V.hom).obj ((Over.pullback Q.hom).obj A)).hom := e.inv.w
  have hi : IsIso ((Over.pullback V.hom).obj ((Over.pullback Q.hom).obj A)).hom.appTop := by
    rw [← he, Scheme.Hom.comp_appTop]
    infer_instance
  let d := pullbackSymmetry V.hom ((Over.pullback Q.hom).obj A).hom
  have : IsIso d.hom.appTop := inferInstanceAs (IsIso (Scheme.Γ.map d.hom.op))
  have hd : d.hom ≫ ((Over.pullback V.hom).obj ((Over.pullback Q.hom).obj A)).hom =
      (fst V ((Over.pullback Q.hom).obj A)).left :=
    pullbackSymmetry_hom_comp_snd V.hom ((Over.pullback Q.hom).obj A).hom
  rw [← hd, Scheme.Hom.comp_appTop]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RelativeProperFunctions.Construction
