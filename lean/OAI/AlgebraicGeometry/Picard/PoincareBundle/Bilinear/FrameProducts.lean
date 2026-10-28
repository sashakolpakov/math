import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport

/-! # Frame Products -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.FrameProducts

noncomputable section

/-!
# Multiplicative normalized frames remain multiplicative under actual pullback and fiber comparison
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits

variable {X : Scheme.{u}} {M N P : X.Modules}

/-- The sectionwise product of two normalized frames is an equality of actual structure-sheaf maps. -/
theorem product_iff (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N) (u : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ P) :
    (∀ U : X.Opens, β.app U (s.app U (1 : Γ(X, U))) (t.app U (1 : Γ(X, U))) =
      u.app U (1 : Γ(X, U))) ↔ t ≫ Contraction.contractLeft β s = u := by
  constructor
  · intro h
    apply Line.FrameUnits.unit_hom_ext
    intro U
    change (Contraction.contractLeft β s).app U (t.app U (1 : Γ(X, U))) = u.app U (1 : Γ(X, U))
    rw [Contraction.contractLeft_app]
    exact h U
  · intro h U
    have he := congrArg (fun a : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ P => a.app U (1 : Γ(X, U))) h
    change (Contraction.contractLeft β s).app U (t.app U (1 : Γ(X, U))) = u.app U (1 : Γ(X, U)) at he
    rw [Contraction.contractLeft_app] at he
    exact he

/-- Pullback of a normalized section commutes with postcomposition by an actual module-sheaf map. -/
theorem pulledSection_comp {Y : Scheme.{u}} (f : Y ⟶ X) {Q : X.Modules}
    (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N) (a : N ⟶ Q) :
    ContractionPullback.pulledSection f (t ≫ a) = ContractionPullback.pulledSection f t ≫ (Scheme.Modules.pullback f).map a := by
  unfold ContractionPullback.pulledSection
  rw [Functor.map_comp, Category.assoc]

/-- Actual pullback preserves the multiplication equation of normalized frames. -/
theorem product_pullback {Y : Scheme.{u}} (f : Y ⟶ X)
    (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N)
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N)
    (u : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ P)
    (h : ∀ U : X.Opens, β.app U (s.app U (1 : Γ(X, U))) (t.app U (1 : Γ(X, U))) =
      u.app U (1 : Γ(X, U))) :
    ∀ U : Y.Opens, (BilinearPullback.pullback f hM hN β).app U
      ((ContractionPullback.pulledSection f s).app U (1 : Γ(Y, U))) ((ContractionPullback.pulledSection f t).app U (1 : Γ(Y, U))) =
        (ContractionPullback.pulledSection f u).app U (1 : Γ(Y, U)) := by
  apply (product_iff _ _ _ _).mpr
  have hp := (product_iff β s t u).mp h
  calc
    ContractionPullback.pulledSection f t ≫ Contraction.contractLeft (BilinearPullback.pullback f hM hN β) (ContractionPullback.pulledSection f s) =
        ContractionPullback.pulledSection f t ≫ (Scheme.Modules.pullback f).map (Contraction.contractLeft β s) :=
      congrArg (fun a => ContractionPullback.pulledSection f t ≫ a) (ContractionPullback.contractLeft_pullback f hN hM β s).symm
    _ = ContractionPullback.pulledSection f (t ≫ Contraction.contractLeft β s) := (pulledSection_comp f t _).symm
    _ = ContractionPullback.pulledSection f u := congrArg (ContractionPullback.pulledSection f) hp

/-- A change of actual fiber isomorphisms preserves the normalized-frame multiplication equation. -/
theorem product_transport {M' N' P' : X.Modules} (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P)
    (a : M ≅ M') (b : N ≅ N') (c : P ≅ P')
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N) (u : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ P)
    (h : ∀ U : X.Opens, β.app U (s.app U (1 : Γ(X, U))) (t.app U (1 : Γ(X, U))) =
      u.app U (1 : Γ(X, U))) :
    ∀ U : X.Opens, (Transport.transport β a b c).app U
      ((s ≫ a.hom).app U (1 : Γ(X, U))) ((t ≫ b.hom).app U (1 : Γ(X, U))) =
        (u ≫ c.hom).app U (1 : Γ(X, U)) := by
  apply (product_iff _ _ _ _).mpr
  rw [Transport.contractLeft_transport]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, (product_iff β s t u).mp h]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.FrameProducts
