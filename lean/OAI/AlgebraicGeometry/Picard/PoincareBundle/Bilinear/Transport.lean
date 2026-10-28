import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionPullback

/-! # Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport

noncomputable section

/-!
# Changing actual line-bundle fibers in bilinear structure maps
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

section

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps

variable {X : Scheme.{u}} {M M' N N' P P' : X.Modules}
  (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) (a : M ≅ M') (b : N ≅ N') (c : P ≅ P')

/-- Transport a bilinear structure map through the three specified actual sheaf isomorphisms. -/
def transport : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M' N' P' := (β.precomp a.inv b.inv).postcomp c.hom

/-- Transport of the bilinear operation is the corresponding exact tensor morphism. -/
theorem toHom_transport : BilinearPullback.toHom (transport β a b c) = Tensor.SheafMaps.tensorMap a.inv b.inv ≫ BilinearPullback.toHom β ≫ c.hom := by
  unfold transport
  rw [BilinearPullback.toHom_postcomp, BilinearPullback.toHom_precomp, Category.assoc]

/-- Inserting the same section after changing fibers gives the transported contraction morphism. -/
theorem contractLeft_transport (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) :
    Contraction.contractLeft (transport β a b c) (s ≫ a.hom) = b.inv ≫ Contraction.contractLeft β s ≫ c.hom := by
  apply Scheme.Modules.hom_ext
  intro U
  ext n
  change (Contraction.contractLeft (transport β a b c) (s ≫ a.hom)).app U n =
    c.hom.app U ((Contraction.contractLeft β s).app U (b.inv.app U n))
  rw [Contraction.contractLeft_app, Contraction.contractLeft_app]
  have ha : a.inv.app U (a.hom.app U (s.app U (1 : Γ(X, U)))) = s.app U (1 : Γ(X, U)) :=
    congrArg (fun t => t.app U (s.app U (1 : Γ(X, U)))) a.hom_inv_id
  change c.hom.app U (β.app U (a.inv.app U (a.hom.app U (s.app U (1 : Γ(X, U)))) ) (b.inv.app U n)) = _
  rw [ha]

end

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionPullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M N P : Y.Modules} {M' N' P' : X.Modules}
  (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N) (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P)
  (a : (Scheme.Modules.pullback f).obj M ≅ M')
  (b : (Scheme.Modules.pullback f).obj N ≅ N')
  (c : (Scheme.Modules.pullback f).obj P ≅ P') (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ M)

/-- Pulling back the bilinear operation, its section, and its fibers gives the native transported morphism. -/
theorem contractLeft_pullback_transport :
    Contraction.contractLeft (transport (BilinearPullback.pullback f hM hN β) a b c) (ContractionPullback.pulledSection f s ≫ a.hom) =
      b.inv ≫ (Scheme.Modules.pullback f).map (Contraction.contractLeft β s) ≫ c.hom := by
  rw [contractLeft_transport, ← ContractionPullback.contractLeft_pullback f hN hM β s]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport
