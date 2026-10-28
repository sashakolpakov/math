import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.AlgebraTransport

/-! # Equivariance Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.EquivarianceTransport

noncomputable section

/-!
# Recover bilinear equivariance from its actual line-fiber presentations
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.AlgebraTransport

variable {T : Scheme.{u}}

/-- Equivariance after actual fiber identifications gives equivariance for the original pulled sheaf maps. -/
theorem of_transport {M N P M' N' P' A B C A' B' C' : T.Modules}
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) (γ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M' N' P')
    (a : M ≅ A) (b : N ≅ B) (c : P ≅ C) (a' : M' ≅ A') (b' : N' ≅ B') (c' : P' ≅ C')
    (u : A ⟶ A') (v : B ⟶ B') (w : C ⟶ C')
    (h : (Transport.transport γ a' b' c').precomp u v = (Transport.transport β a b c).postcomp w) :
    γ.precomp (a.hom ≫ u ≫ a'.inv) (b.hom ≫ v ≫ b'.inv) = β.postcomp (c.hom ≫ w ≫ c'.inv) := by
  apply AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.ext
  intro U
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro n
  have hh := congrArg (fun δ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap A B C' =>
    δ.app U (a.hom.app U m) (b.hom.app U n)) h
  have he := congrArg (fun z => c'.inv.app U z) hh
  change c'.inv.app U (c'.hom.app U (γ.app U
      (a'.inv.app U (u.app U (a.hom.app U m))) (b'.inv.app U (v.app U (b.hom.app U n))))) =
    c'.inv.app U (w.app U (c.hom.app U (β.app U
      (a.inv.app U (a.hom.app U m)) (b.inv.app U (b.hom.app U n))))) at he
  rw [AlgebraTransport.inv_hom_app, AlgebraTransport.inv_hom_app, AlgebraTransport.inv_hom_app] at he
  exact he

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.EquivarianceTransport
