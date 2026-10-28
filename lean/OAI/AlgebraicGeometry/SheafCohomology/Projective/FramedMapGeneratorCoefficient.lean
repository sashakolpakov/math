import OAI.AlgebraicGeometry.SheafCohomology.Projective.FramedGlobalTensorProduct

/-! # Framed Map Generator Coefficient -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FramedMapGeneratorCoefficient

noncomputable section

/-! The image of a normalized local generator determines a global section map's coefficient. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

theorem overFrameMap_globalCoefficient_of_generator {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens)
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : Γ(M, ⊤)) (t : Γ(N, ⊤)) (c : Γ(X, U))
    (hs : FrameSections.overTrivializationCoefficient M U eM s = 1)
    (ht : FrameSections.overTrivializationCoefficient N U eN t = 1)
    (hf : f.val.app (op U) (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) =
      c • N.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t)
    (x : Γ(M, ⊤)) :
    FrameSections.overTrivializationCoefficient N U eN (f.val.app (op ⊤) x) =
      c * FrameSections.overTrivializationCoefficient M U eM x := by
  erw [RankOneMapCoordinates.overFrameMap_global_coordinate]
  have hc : RankOneMapCoordinates.overFrameMapCoefficient U eM eN f = c := by
    unfold RankOneMapCoordinates.overFrameMapCoefficient RankOneMapCoordinates.rankOneMapCoefficient
    erw [FramedGlobalTensorProduct.overFrame_one_eq_restrict M U eM s hs, hf,
      (RankOneMapCoordinates.overFrameSectionEquiv N U eN).symm.map_smul]
    change c * FrameSections.overTrivializationCoefficient N U eN t = c
    rw [ht, mul_one]
  rw [hc]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FramedMapGeneratorCoefficient
