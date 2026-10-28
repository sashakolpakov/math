import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.SheafPairing
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafBlocks

/-! # Intrinsic Adjoints -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.IntrinsicAdjoints.Construction

noncomputable section

/-! Adjointness of actual CartierDuality torsion-sheaf maps gives adjointness on
the same native torsion schemes, preserving every test-scheme value. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

set_option backward.isDefEq.respectTransparency false in
theorem torsionSheafPairingToNative_adjoint {S : Scheme.{u}}
    (G H : Grp (Over S)) [IsCommMonObj G.X] [IsCommMonObj H.X] (n : ℕ)
    (e : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n)
      (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S H) n))
    (p : G ⟶ G) (r : H ⟶ H)
    (he : CartierDuality.SheafBlocks.Construction.Schemes.ProjectorsAdjoint e (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap p) n)
      (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap r) n))
    (T : Over S) (x : T ⟶ Groups.Construction.nativeTorsionScheme G.X n) (y : T ⟶ Groups.Construction.nativeTorsionScheme H.X n) :
    (SheafPairing.Construction.torsionSheafPairingToNative G H n e).pairValue (x ≫ Groups.Construction.nativeTorsionMap n p.hom.hom) y =
      (SheafPairing.Construction.torsionSheafPairingToNative G H n e).pairValue x (y ≫ Groups.Construction.nativeTorsionMap n r.hom.hom) := by
  have hx := congrArg (fun f => f.hom.app (.op T) (ULift.up x)) (SheafComparison.Construction.kernelTorsionSheafIso_natural n p)
  have hy := congrArg (fun f => f.hom.app (.op T) (ULift.up y)) (SheafComparison.Construction.kernelTorsionSheafIso_natural n r)
  change (SheafComparison.Construction.kernelTorsionSheafIso G n).hom.hom.app (.op T) (ULift.up (x ≫ Groups.Construction.nativeTorsionMap n p.hom.hom)) =
    (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap p) n).hom.app (.op T)
      ((SheafComparison.Construction.kernelTorsionSheafIso G n).hom.hom.app (.op T) (ULift.up x)) at hx
  change (SheafComparison.Construction.kernelTorsionSheafIso H n).hom.hom.app (.op T) (ULift.up (y ≫ Groups.Construction.nativeTorsionMap n r.hom.hom)) =
    (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap r) n).hom.app (.op T)
      ((SheafComparison.Construction.kernelTorsionSheafIso H n).hom.hom.app (.op T) (ULift.up y)) at hy
  apply ULift.up_injective
  rw [SheafPairing.Construction.torsionSheafPairingToNative_rightValue, SheafPairing.Construction.torsionSheafPairingToNative_rightValue, hx, hy]
  exact he T _ _

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.IntrinsicAdjoints.Construction
