import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.SheafPairing

/-! # Sheaf Actions -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.SheafActions.Construction

noncomputable section

/-!
The canonical torsion-kernel comparison transports the actual CartierDuality
adjoint and alternating identities to IsogenyQuotient's native scheme pairing.
The native maps are restrictions of the original group homomorphisms.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem kernelTorsionSheafIso_apply_map
    {S : Scheme.{u}} {G K : Grp (Over S)} [IsCommMonObj G.X] [IsCommMonObj K.X]
    (n : ℕ) (f : G ⟶ K) (T : Over S) (x : T ⟶ Groups.Construction.nativeTorsionScheme G.X n) :
    (SheafComparison.Construction.kernelTorsionSheafIso K n).hom.hom.app (.op T) (ULift.up (x ≫ Groups.Construction.nativeTorsionMap n f.hom.hom)) =
      (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap f) n).hom.app (.op T)
        ((SheafComparison.Construction.kernelTorsionSheafIso G n).hom.hom.app (.op T) (ULift.up x)) :=
  congrArg (fun a : CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (SheafComparison.Construction.kernelTorsionGroup G n) ⟶
    CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S K) n => a.hom.app (.op T) (ULift.up x))
      (SheafComparison.Construction.kernelTorsionSheafIso_natural n f)

theorem torsionSheafPairingToNative_adjoint
    {S : Scheme.{u}} (G K : Grp (Over S)) [IsCommMonObj G.X] [IsCommMonObj K.X]
    (n : ℕ) (e : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n)
      (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S K) n))
    (p : G ⟶ G) (q : K ⟶ K)
    (hadj : CartierDuality.SheafBlocks.Construction.Schemes.ProjectorsAdjoint e (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap p) n)
      (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap q) n))
    (T : Over S) (x : T ⟶ Groups.Construction.nativeTorsionScheme G.X n) (y : T ⟶ Groups.Construction.nativeTorsionScheme K.X n) :
    (SheafPairing.Construction.torsionSheafPairingToNative G K n e).pairValue (x ≫ Groups.Construction.nativeTorsionMap n p.hom.hom) y =
      (SheafPairing.Construction.torsionSheafPairingToNative G K n e).pairValue x (y ≫ Groups.Construction.nativeTorsionMap n q.hom.hom) := by
  let ix := (SheafComparison.Construction.kernelTorsionSheafIso G n).hom.hom.app (.op T) (ULift.up x)
  let iy := (SheafComparison.Construction.kernelTorsionSheafIso K n).hom.hom.app (.op T) (ULift.up y)
  have hp := kernelTorsionSheafIso_apply_map n p T x
  have hq := kernelTorsionSheafIso_apply_map n q T y
  have hl := congrArg
    (CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n) T
      (e.rightAdjoint.hom.app (.op T) iy)) hp
  have hr := congrArg
    (fun z : (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S K) n).obj.obj (.op T) =>
      CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n) T
        (e.rightAdjoint.hom.app (.op T) z) ix) hq.symm
  exact congrArg ULift.down
    ((SheafPairing.Construction.torsionSheafPairingToNative_rightValue G K n e T (x ≫ Groups.Construction.nativeTorsionMap n p.hom.hom) y).trans
      (hl.trans ((hadj T ix iy).trans
        (hr.trans (SheafPairing.Construction.torsionSheafPairingToNative_rightValue G K n e T x
          (y ≫ Groups.Construction.nativeTorsionMap n q.hom.hom)).symm))))

theorem torsionSheafPairingToNative_alternating
    {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X]
    (n : ℕ) (e : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n)
      (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n))
    (halt : ∀ (T : Over S) (x : (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n).obj.obj (.op T)),
      CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.TorsionSheaves.Construction.Schemes.torsionFppfAb (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n) T
        (e.rightAdjoint.hom.app (.op T) x) x = 1)
    (T : Over S) (x : T ⟶ Groups.Construction.nativeTorsionScheme G.X n) :
    (SheafPairing.Construction.torsionSheafPairingToNative G G n e).pairValue x x = 1 :=
  congrArg ULift.down ((SheafPairing.Construction.torsionSheafPairingToNative_rightValue G G n e T x x).trans (halt T _))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.SheafActions.Construction
