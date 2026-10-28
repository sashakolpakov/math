import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.RestrictionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.SheafificationRestrictionHom

/-! # Sheaf Restriction Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.SheafRestrictionCoordinates

noncomputable section

/-! Native section coordinates identify restricted sheaf presentation cochains with the actual tuple restriction maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

variable {C D : Type (max u v)} [Category.{v} C] [Category.{v} D]
  [HasBinaryProducts C] [HasBinaryProducts D] (G : C ⥤ D) {ι : Type v}
  (F : ι → C) (H : ι → D) (a : ∀ i, G.obj (F i) ⟶ H i)
  (R : Type (max u v)) [CommRing R] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] [G.IsCocontinuous J K]
  [∀ (A : Cᵒᵖ ⥤ ModuleCat.{max u v} R), G.op.HasPointwiseRightKanExtension A]
  (n : ℕ) (t : Fin (n + 1) → ι)
  (b : G.obj (TupleProducts.family F n t) ⟶ TupleProducts.family H n t)
  (hb : ∀ j, b ≫ Pi.π (fun j => H (t j)) j = G.map (Pi.π (fun j => F (t j)) j) ≫ a (t j))
  (M : Sheaf K (ModuleCat.{max u v} R))
  (f : (CoveringPresentationResolution.complex K R H).X n ⟶ M)

include hb in
theorem coordinate : ResolutionCoordinates.sheaf F R n J
    ((Cech.PresentationSheafRestriction.restriction R G J K).obj M)
    (((Cech.PresentationSheafRestriction.map R G J K (FamilyMap.Family.map G F H a)).f n) ≫
      (Cech.PresentationSheafRestriction.restriction R G J K).map f) t =
        M.obj.map b.op (ResolutionCoordinates.sheaf H R n K M f t) := by
  have hu := SheafificationRestrictionHom.hom R G J K
    ((Cech.PresentationRestriction.map R G (FamilyMap.Family.map G F H a)).f n) f
  exact (congrArg (fun c => ResolutionCoordinates.presheaf F R n (G.op ⋙ M.obj) c t) hu).trans
    (RestrictionCoordinates.presheaf G F H a n t b hb R M.obj
      (ResolutionCoordinates.unadjoint H R n K M f))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.SheafRestrictionCoordinates
