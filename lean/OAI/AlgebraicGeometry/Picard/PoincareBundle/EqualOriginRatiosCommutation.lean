import OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.ProductOriginTransport

/-! # Equal Origin Ratios Commutation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.EqualOriginRatiosCommutation

noncomputable section

/-! Equal actual origin coefficients and a symmetric line product force equality of the two translation paths. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.IsoRatios OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction

variable {X : Scheme.{u}} {M N P Z : X.Modules}

/-- The common origin factor is obtained from the equality of coefficients of actual isomorphisms. -/
theorem common_origin_factor (hZ : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle Z)
    (a : Z ≅ M) (b : Z ≅ N) (r : Z ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ N)
    (he : Line.IsoRatios.ratio hZ a (r ≪≫ s) = Line.IsoRatios.ratio hZ b (r ≪≫ t)) :
    ∃ q : Z ⟶ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X, a.hom = q ≫ s.hom ∧ b.hom = q ≫ t.hom := by
  let q := Isogenies.NeighborCounting.ModuleScalar.scalarEnd Z (Line.IsoRatios.ratio hZ a (r ≪≫ s)).val ≫ r.hom
  refine ⟨q, ?_, ?_⟩
  · exact (Line.IsoRatios.ratio_spec hZ a (r ≪≫ s)).symm.trans (Category.assoc _ _ _).symm
  · have hb := Line.IsoRatios.ratio_spec hZ b (r ≪≫ t)
    rw [← he] at hb
    exact hb.symm.trans (Category.assoc _ _ _).symm

/-- The two genuine sheaf-isomorphism paths commute once the origin ratios are equal. -/
theorem paths_commute (hZ : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle Z)
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) (γ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap N M P)
    (hs : ∀ (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)), β.app U m n = γ.app U n m)
    (a : Z ≅ M) (b : Z ≅ N) (u : M ≅ P) (v : N ≅ P)
    (r : Z ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ N)
    (he : Line.IsoRatios.ratio hZ a (r ≪≫ s) = Line.IsoRatios.ratio hZ b (r ≪≫ t))
    (hu : u.hom = Bilinear.Contraction.contractLeft γ t.hom) (hv : v.hom = Bilinear.Contraction.contractLeft β s.hom) :
    a ≪≫ u = b ≪≫ v := by
  obtain ⟨q, ha, hb⟩ := common_origin_factor hZ a b r s t he
  apply Iso.ext
  change a.hom ≫ u.hom = b.hom ≫ v.hom
  rw [hu, hv]
  exact Symmetric.ProductOriginTransport.origin_commutation β γ hs q s.hom t.hom a.hom b.hom ha hb

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.EqualOriginRatiosCommutation
