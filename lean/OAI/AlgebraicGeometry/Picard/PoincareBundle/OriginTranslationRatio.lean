import OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.ProductOriginTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RightContraction

/-! # Origin Translation Ratio -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.OriginTranslationRatio

noncomputable section

/-! The origin coefficient of a bilinear translation is the coefficient of its right-contraction automorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.IsoRatios OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.AutomorphismUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction
open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RightContraction.Construction

variable {X : Scheme.{u}} {M Z : X.Modules}

/-- The two contractions of a bilinear product have the same value on the two chosen frames. -/
theorem frame_square (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M Z M)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) (o : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ Z)
    (a : Z ≅ M) (c : M ≅ M)
    (ha : a.hom = Bilinear.Contraction.contractLeft β s.hom) (hc : c.hom = AbelianScheme.IsogenyQuotient.RightContraction.Construction.lineContractRight β o.hom) :
    o ≪≫ a = s ≪≫ c := by
  apply Iso.ext
  change o.hom ≫ a.hom = s.hom ≫ c.hom
  rw [ha, hc]
  exact Symmetric.ProductOriginTransport.contraction_exchange β (AbelianScheme.IsogenyQuotient.BilinearFlip.Construction.flipLineBilinear β)
    (fun _ _ _ => rfl) s.hom o.hom

/-- The scalar relating actual origin translation to the chosen frame is exactly the scalar of
the actual neutral-row automorphism; no equality of coefficients is assumed. -/
theorem ratio_eq (hZ : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle Z) (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M)
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M Z M) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) (o : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ Z)
    (a : Z ≅ M) (c : M ≅ M)
    (ha : a.hom = Bilinear.Contraction.contractLeft β s.hom) (hc : c.hom = AbelianScheme.IsogenyQuotient.RightContraction.Construction.lineContractRight β o.hom) :
    Line.IsoRatios.ratio hZ a (o.symm ≪≫ s) = Line.AutomorphismUnits.unitOfAut hM c := by
  have hp := congrArg (fun e => o.symm ≪≫ e) (frame_square β s o a c ha hc)
  have he : a = (o.symm ≪≫ s) ≪≫ c := by
    simpa only [Iso.symm_self_id_assoc, Iso.trans_assoc] using hp
  calc
    Line.IsoRatios.ratio hZ a (o.symm ≪≫ s) = Line.IsoRatios.ratio hZ ((o.symm ≪≫ s) ≪≫ c) ((o.symm ≪≫ s) ≪≫ Iso.refl M) := by
      rw [he, Iso.trans_refl]
    _ = Line.IsoRatios.ratio hM c (Iso.refl M) := Line.IsoRatios.ratio_precomp hM hZ (o.symm ≪≫ s) c (Iso.refl M)
    _ = Line.AutomorphismUnits.unitOfAut hM c := by
      change Line.AutomorphismUnits.unitOfAut hM (c ≪≫ Iso.refl M) = Line.AutomorphismUnits.unitOfAut hM c
      rw [Iso.trans_refl]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.OriginTranslationRatio
