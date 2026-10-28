import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Ideal
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Closed Transform Map -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ClosedTransformMap.Construction

noncomputable section

/-! Actual maps from controlled closed subschemes to the original closed subscheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def closedTransformMap {X Y : Scheme.{u}} (π : Y ⟶ X)
    (H : X.IdealSheafData) (L : Y.IdealSheafData) (h : H.comap π ≤ L) : L.subscheme ⟶ H.subscheme :=
  Scheme.IdealSheafData.inclusion h ≫ (H.comapIso π).hom ≫ pullback.snd π H.subschemeι

theorem closedTransformMap_over {X Y : Scheme.{u}} (π : Y ⟶ X)
    (H : X.IdealSheafData) (L : Y.IdealSheafData) (h : H.comap π ≤ L) :
    closedTransformMap π H L h ≫ H.subschemeι = L.subschemeι ≫ π := by
  simp only [closedTransformMap, Category.assoc, ← pullback.condition,
    Scheme.IdealSheafData.comapIso_hom_fst_assoc, Scheme.IdealSheafData.inclusion_subschemeι_assoc]

theorem closedTransformMap_isProper {X Y : Scheme.{u}} (π : Y ⟶ X) [IsProper π]
    (H : X.IdealSheafData) (L : Y.IdealSheafData) (h : H.comap π ≤ L) :
    IsProper (closedTransformMap π H L h) := by
  let : IsProper (closedTransformMap π H L h ≫ H.subschemeι) :=
    (closedTransformMap_over π H L h).symm ▸ inferInstanceAs (IsProper (L.subschemeι ≫ π))
  exact IsProper.of_comp (closedTransformMap π H L h) H.subschemeι

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ClosedTransformMap.Construction
