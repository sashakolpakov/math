import OAI.AlgebraicGeometry.SheafCohomology.Projective.FramedTensorMap
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFrameSections

/-! # Framed Global Tensor Product -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FramedGlobalTensorProduct

noncomputable section

/-! A tensor map carrying coefficient-one generators to a coefficient-one generator multiplies coefficients. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
universe u
local instance framedGlobalTensorMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

theorem tensorMap_restrict {X : Scheme.{u}} {M N P : X.Modules}
    (f : M ⊗ N ⟶ P) (U : X.Opens) (x : Γ(M, ⊤)) (y : Γ(N, ⊤)) :
    P.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (f.val.app (op ⊤) (TensorSections.tensorSection M N ⊤ x y)) =
    f.val.app (op U) (TensorSections.tensorSection M N U
      (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op x)
      (N.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op y)) := by
  have h := PresheafOfModules.naturality_apply f.val
    (homOfLE (le_top : U ≤ ⊤)).op (TensorSections.tensorSection M N ⊤ x y)
  rw [TensorSections.tensorSection_restrict] at h
  exact h.symm

theorem overFrame_one_eq_restrict {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : Γ(M, ⊤)) (hs : FrameSections.overTrivializationCoefficient M U e s = 1) :
    (RankOneMapCoordinates.overFrameSectionEquiv M U e) 1 =
      M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s := by
  have h := (RankOneMapCoordinates.overFrameSectionEquiv M U e).apply_symm_apply
    (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s)
  change (RankOneMapCoordinates.overFrameSectionEquiv M U e) (FrameSections.overTrivializationCoefficient M U e s) = _ at h
  rw [hs] at h
  exact h

theorem tensorMap_globalCoefficient {X : Scheme.{u}} {M N P : X.Modules}
    (f : M ⊗ N ⟶ P) (U : X.Opens)
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eP : P.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : Γ(M, ⊤)) (t : Γ(N, ⊤)) (u : Γ(P, ⊤))
    (hs : FrameSections.overTrivializationCoefficient M U eM s = 1)
    (ht : FrameSections.overTrivializationCoefficient N U eN t = 1)
    (hu : FrameSections.overTrivializationCoefficient P U eP u = 1)
    (hf : f.val.app (op ⊤) (TensorSections.tensorSection M N ⊤ s t) = u)
    (x : Γ(M, ⊤)) (y : Γ(N, ⊤)) :
    FrameSections.overTrivializationCoefficient P U eP
      (f.val.app (op ⊤) (TensorSections.tensorSection M N ⊤ x y)) =
      FrameSections.overTrivializationCoefficient M U eM x * FrameSections.overTrivializationCoefficient N U eN y := by
  change (RankOneMapCoordinates.overFrameSectionEquiv P U eP).symm
    (P.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (f.val.app (op ⊤) (TensorSections.tensorSection M N ⊤ x y))) = _
  rw [tensorMap_restrict, FramedTensorMap.overFrameTensorMap_coordinate,
    overFrame_one_eq_restrict M U eM s hs, overFrame_one_eq_restrict N U eN t ht,
    ← tensorMap_restrict, hf]
  change (FrameSections.overTrivializationCoefficient M U eM x * FrameSections.overTrivializationCoefficient N U eN y) *
    FrameSections.overTrivializationCoefficient P U eP u = _
  rw [hu, mul_one]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FramedGlobalTensorProduct
