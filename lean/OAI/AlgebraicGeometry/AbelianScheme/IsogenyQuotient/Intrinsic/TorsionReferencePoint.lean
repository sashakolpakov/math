import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BilinearPullbackAdjunction

/-! # Torsion Reference Point -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionReferencePoint.Construction

noncomputable section

/-! The original point of a base-changed torsion point retains its
literal inclusion into the original group scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
attribute [local instance] PairingBaseChange.Construction.pulledbackGroup_commutative TorsionBaseChange.Construction.nativeTorsionPullback_commutative

variable {S S' : Scheme.{u}} (s : S' ⟶ S) (G : Grp (Over S)) [IsCommMonObj G.X]
  (n : ℕ) (T : Over S')

def nativeTorsionOriginalPoint
    (x : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme ((Over.pullback s).obj G.X) n) :
    (Over.map s).obj T ⟶ Torsion.Groups.Construction.nativeTorsionScheme G.X n :=
  (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (Torsion.SheafComparison.Construction.kernelTorsionGroup G n) T).symm
    (x ≫ (TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso s G n).inv.hom.hom)

set_option backward.isDefEq.respectTransparency false in
theorem nativeTorsionOriginalPoint_inclusion
    (x : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme ((Over.pullback s).obj G.X) n) :
    nativeTorsionOriginalPoint s G n T x ≫ Torsion.Groups.Construction.nativeTorsionInclusion G.X n =
      (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s G T).symm
        (x ≫ Torsion.Groups.Construction.nativeTorsionInclusion ((Over.pullback s).obj G.X) n) := by
  let i : Torsion.SheafComparison.Construction.kernelTorsionGroup G n ⟶ G := Grp.homMk (Torsion.Groups.Construction.nativeTorsionInclusion G.X n)
  have h := CartierDuality.EvaluationBaseChange.Construction.Schemes.pullbackPointMulEquiv_symm_comp s i T
    (x ≫ (TorsionBaseChange.Construction.nativeTorsionBaseChangeGroupIso s G n).inv.hom.hom)
  exact h.symm.trans (congrArg (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s G T).symm
    ((Category.assoc x (TorsionBaseChange.Construction.nativeTorsionBaseChangeIso s G n).inv
      ((Over.pullback s).map (Torsion.Groups.Construction.nativeTorsionInclusion G.X n))).trans
        (congrArg (fun a => x ≫ a) (TorsionBaseChange.Construction.nativeTorsionBaseChangeIso_inv_inclusion s G n))))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionReferencePoint.Construction
