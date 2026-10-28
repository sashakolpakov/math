import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSectionBilinear
import OAI.AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates

/-! # Framed Tensor Map -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FramedTensorMap

noncomputable section

/-! Bilinear maps of locally framed sheaf modules act by their coefficient on the frame generators. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
universe u v

theorem linearEquiv_eq_smul_one {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (e : R ≃ₗ[R] M) (x : M) :
    x = e.symm x • e 1 := by
  rw [← e.map_smul, smul_eq_mul, mul_one, e.apply_symm_apply]

theorem rankOne_eq_smul_of_normalized_functional {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (e : R ≃ₗ[R] M)
    (p : M → R) (hp : ∀ (r : R) (x : M), p (r • x) = r * p x)
    (s : M) (hs : p s = 1) (x : M) : x = p x • s := by
  have hpx : p x = e.symm x * p (e 1) := by
    conv_lhs => rw [linearEquiv_eq_smul_one e x, hp]
  have hps : e.symm s * p (e 1) = 1 := by
    rw [← hp, ← linearEquiv_eq_smul_one e s, hs]
  apply e.symm.injective
  rw [e.symm.map_smul, hpx]
  change e.symm x = (e.symm x * p (e 1)) * e.symm s
  rw [mul_assoc, mul_comm (p (e 1)) (e.symm s), hps, mul_one]

local instance framedTensorMapMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

theorem overFrameTensorMap_coordinate {X : Scheme.{u}} {M N P : X.Modules}
    (U : X.Opens)
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eP : P.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (f : M ⊗ N ⟶ P) (x : Γ(M, U)) (y : Γ(N, U)) :
    (RankOneMapCoordinates.overFrameSectionEquiv P U eP).symm
      (f.val.app (op U) (TensorSections.tensorSection M N U x y)) =
    ((RankOneMapCoordinates.overFrameSectionEquiv M U eM).symm x * (RankOneMapCoordinates.overFrameSectionEquiv N U eN).symm y) *
      (RankOneMapCoordinates.overFrameSectionEquiv P U eP).symm
        (f.val.app (op U) (TensorSections.tensorSection M N U
          ((RankOneMapCoordinates.overFrameSectionEquiv M U eM) 1) ((RankOneMapCoordinates.overFrameSectionEquiv N U eN) 1))) := by
  let qM := RankOneMapCoordinates.overFrameSectionEquiv M U eM
  let qN := RankOneMapCoordinates.overFrameSectionEquiv N U eN
  let qP := RankOneMapCoordinates.overFrameSectionEquiv P U eP
  have hx := linearEquiv_eq_smul_one qM x
  have hy := linearEquiv_eq_smul_one qN y
  change qP.symm (f.val.app (op U) (TensorSections.tensorSection M N U x y)) = _
  conv_lhs => rw [hx, hy, TensorSectionBilinear.tensorSection_smul_both]
  rw [map_smul, qP.symm.map_smul]
  rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FramedTensorMap
