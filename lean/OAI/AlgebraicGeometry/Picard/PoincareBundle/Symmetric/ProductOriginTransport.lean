import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.FrameProducts
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.IsoRatios

/-! # Product Origin Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.ProductOriginTransport

noncomputable section

/-! A symmetric actual line product makes the two translations from a commonly normalized origin commute. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits

variable {X : Scheme.{u}} {M N P Z : X.Modules}
  (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) (γ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap N M P)
  (hs : ∀ (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)), β.app U m n = γ.app U n m)

include hs

/-- Swapping both inserted sections leaves the actual product morphism unchanged. -/
theorem contraction_exchange (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N) :
    t ≫ Bilinear.Contraction.contractLeft β s = s ≫ Bilinear.Contraction.contractLeft γ t := by
  apply Line.FrameUnits.unit_hom_ext
  intro U
  change (Bilinear.Contraction.contractLeft β s).app U (t.app U (1 : Γ(X, U))) =
    (Bilinear.Contraction.contractLeft γ t).app U (s.app U (1 : Γ(X, U)))
  rw [Bilinear.Contraction.contractLeft_app, Bilinear.Contraction.contractLeft_app]
  exact hs U _ _

/-- Any common origin factor cancels from the comparison of the two actual translation paths. -/
theorem origin_commutation (r : Z ⟶ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N) (a : Z ⟶ M) (b : Z ⟶ N)
    (ha : a = r ≫ s) (hb : b = r ≫ t) :
    a ≫ Bilinear.Contraction.contractLeft γ t = b ≫ Bilinear.Contraction.contractLeft β s := by
  rw [ha, hb, Category.assoc, Category.assoc, contraction_exchange β γ hs s t]

/-- The resulting equality compares coefficients of actual isomorphisms, without a cocycle hypothesis. -/
theorem defect_symmetry (hZ : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle Z)
    (a : Z ≅ M) (b : Z ≅ N) (u : M ≅ P) (v : N ≅ P) (w : Z ≅ P)
    (r : Z ⟶ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N)
    (ha : a.hom = r ≫ s) (hb : b.hom = r ≫ t)
    (hu : u.hom = Bilinear.Contraction.contractLeft γ t) (hv : v.hom = Bilinear.Contraction.contractLeft β s) :
    Line.IsoRatios.ratio hZ (a ≪≫ u) w = Line.IsoRatios.ratio hZ (b ≪≫ v) w := by
  have he : a ≪≫ u = b ≪≫ v := by
    apply Iso.ext
    change a.hom ≫ u.hom = b.hom ≫ v.hom
    rw [hu, hv]
    exact origin_commutation β γ hs r s t a.hom b.hom ha hb
  exact congrArg (fun e => Line.IsoRatios.ratio hZ e w) he

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.ProductOriginTransport
