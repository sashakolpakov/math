import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ActionLaws
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport

/-! # Algebra Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.AlgebraTransport

noncomputable section

/-!
# Unit and associativity laws of actual bilinear operations survive a change of line fibers
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction

variable {X : Scheme.{u}}

/-- Inverse fiber maps cancel on actual sections. -/
theorem inv_hom_app {M N : X.Modules} (e : M ≅ N) (U : X.Opens) (m : Γ(M, U)) :
    e.inv.app U (e.hom.app U m) = m :=
  congrArg (fun a => a.app U m) e.hom_inv_id

/-- The actual bilinear left-unit law is invariant under the three relevant fiber identifications. -/
theorem unit_left {M N M' N' : X.Modules} (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N N)
    (a : M ≅ M') (b : N ≅ N') (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (h : ∀ (U : X.Opens) (n : Γ(N, U)), β.app U (s.app U (1 : Γ(X, U))) n = n)
    (U : X.Opens) (n : Γ(N', U)) :
    (Transport.transport β a b b).app U ((s ≫ a.hom).app U (1 : Γ(X, U))) n = n := by
  have hc : Contraction.contractLeft (Transport.transport β a b b) (s ≫ a.hom) = 𝟙 _ := by
    rw [Transport.contractLeft_transport, ActionLaws.contraction_unit β s h,
      Category.id_comp, b.inv_hom_id]
  exact (Contraction.contractLeft_app _ _ U n).symm.trans (congrArg (fun f => f.app U n) hc)

/-- The actual bilinear right-unit law is invariant under fiber identifications. -/
theorem unit_right {M N M' N' : X.Modules} (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N M)
    (a : M ≅ M') (b : N ≅ N') (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N)
    (h : ∀ (U : X.Opens) (m : Γ(M, U)), β.app U m (s.app U (1 : Γ(X, U))) = m)
    (U : X.Opens) (m : Γ(M', U)) :
    (Transport.transport β a b a).app U m ((s ≫ b.hom).app U (1 : Γ(X, U))) = m := by
  change a.hom.app U (β.app U (a.inv.app U m) (b.inv.app U (b.hom.app U (s.app U (1 : Γ(X, U)))))) = m
  rw [inv_hom_app, h]
  exact inv_hom_app a.symm U m

/-- Associativity of actual bilinear structure maps is preserved under consistent changes of every fiber. -/
theorem associative {A B C AB BC D A' B' C' AB' BC' D' : X.Modules}
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap B C BC) (γ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap A BC D)
    (δ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap A B AB) (ε : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap AB C D)
    (a : A ≅ A') (b : B ≅ B') (c : C ≅ C') (ab : AB ≅ AB') (bc : BC ≅ BC') (d : D ≅ D')
    (h : ∀ (U : X.Opens) (x : Γ(A, U)) (y : Γ(B, U)) (z : Γ(C, U)),
      γ.app U x (β.app U y z) = ε.app U (δ.app U x y) z)
    (U : X.Opens) (x : Γ(A', U)) (y : Γ(B', U)) (z : Γ(C', U)) :
    (Transport.transport γ a bc d).app U x ((Transport.transport β b c bc).app U y z) =
      (Transport.transport ε ab c d).app U ((Transport.transport δ a b ab).app U x y) z := by
  change d.hom.app U (γ.app U (a.inv.app U x)
      (bc.inv.app U (bc.hom.app U (β.app U (b.inv.app U y) (c.inv.app U z))))) =
    d.hom.app U (ε.app U (ab.inv.app U (ab.hom.app U (δ.app U (a.inv.app U x) (b.inv.app U y))))
      (c.inv.app U z))
  rw [inv_hom_app, inv_hom_app, h]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.AlgebraTransport
