import OAI.AlgebraicGeometry.SheafCohomology.Projective.FrameSections

/-! # Rank One Map Coordinates -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates

noncomputable section

/-! A map between rank-one frames acts by multiplication by its actual coefficient. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u v w
section Linear
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

def rankOneMapCoefficient (eM : R ≃ₗ[R] M) (eN : R ≃ₗ[R] N) (f : M →ₗ[R] N) : R :=
  eN.symm (f (eM 1))

theorem rankOneMap_coordinate (eM : R ≃ₗ[R] M) (eN : R ≃ₗ[R] N)
    (f : M →ₗ[R] N) (x : M) :
    eN.symm (f x) = rankOneMapCoefficient eM eN f * eM.symm x := by
  have hx : x = (eM.symm x) • eM 1 := by
    rw [← eM.map_smul, smul_eq_mul, mul_one, eM.apply_symm_apply]
  calc
    eN.symm (f x) = eN.symm (f ((eM.symm x) • eM 1)) :=
      congrArg (fun y => eN.symm (f y)) hx
    _ = (eM.symm x) • eN.symm (f (eM 1)) := by
      rw [f.map_smul, eN.symm.map_smul]
    _ = rankOneMapCoefficient eM eN f * eM.symm x :=
      mul_comm (eM.symm x) (eN.symm (f (eM 1)))

end Linear

variable {X : Scheme.{u}}

def overFrameSectionEquiv (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Γ(X, U) ≃ₗ[Γ(X, U)] Γ(M, U) :=
  ((SheafOfModules.evaluation (X.ringCatSheaf.over U) (.op (Over.mk (𝟙 U)))).mapIso e.symm).toLinearEquiv

def overFrameMapCoefficient {M N : X.Modules} (U : X.Opens)
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (f : M ⟶ N) : Γ(X, U) :=
  rankOneMapCoefficient (overFrameSectionEquiv M U eM) (overFrameSectionEquiv N U eN)
    (f.val.app (op U)).hom

theorem overFrameMap_coordinate {M N : X.Modules} (U : X.Opens)
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (f : M ⟶ N)
    (x : Γ(M, U)) :
    (overFrameSectionEquiv N U eN).symm (f.app U x) =
      overFrameMapCoefficient U eM eN f * (overFrameSectionEquiv M U eM).symm x :=
  rankOneMap_coordinate (overFrameSectionEquiv M U eM) (overFrameSectionEquiv N U eN)
    (f.val.app (op U)).hom x

theorem overFrameMap_global_coordinate {M N : X.Modules} (U : X.Opens)
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (f : M ⟶ N)
    (x : Γ(M, ⊤)) :
    FrameSections.overTrivializationCoefficient N U eN (f.app ⊤ x) =
      overFrameMapCoefficient U eM eN f * FrameSections.overTrivializationCoefficient M U eM x := by
  let a := (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op
  have hnat := PresheafOfModules.naturality_apply f.val a x
  change f.app U (M.presheaf.map a x) = N.presheaf.map a (f.app ⊤ x) at hnat
  change (overFrameSectionEquiv N U eN).symm (N.presheaf.map a (f.app ⊤ x)) = _
  rw [← hnat, overFrameMap_coordinate]
  rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.RankOneMapCoordinates
