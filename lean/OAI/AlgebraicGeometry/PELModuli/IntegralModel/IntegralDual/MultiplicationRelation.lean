import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.PairRelation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointEq

/-! # Multiplication Relation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Multiplication of the original universal abelian family preserves
the constructed relation on pairs in the same fiber. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualMulOverlap_target (hrigid : U.PrescribedRigid) :
    U.prescribedDualMulOverlap π ≫ U.prescribedDualOverlapTarget hU π hk =
      U.prescribedDualPairTarget π hU hk ≫ U.prescribedDualMul := by
  let G := U.forgetAuxiliary.data.polarized.dual.abelian.scheme
  let c := DescentCocycleChange.DescentCocycle.source π U.prescribedDualPairProjection
  let f := c ≫ U.prescribedDualPairProjection
  let g := DescentCocycleChange.DescentCocycle.base π U.prescribedDualPairProjection
  have h : f ≫ π = g ≫ π := DescentCocycleChange.DescentCocycle.source_condition π U.prescribedDualPairProjection
  let e := (U.prescribedTransport hU π hk f g h).polarized.dual
  have : IsMonHom e.hom := (U.prescribedTransport hU π hk f g h).polarized.dualGroup
  let p₀ : Over.mk f.left ⟶ G ⊗ G := Over.homMk c.left rfl
  let p₁ : Over.mk g.left ⟶ G ⊗ G := Over.homMk (U.prescribedDualPairTarget π hU hk).left
    (congrArg Over.Hom.left (U.prescribedDualPairTarget_projection π hU hk))
  let x₀ := p₀ ≫ fst G G
  let y₀ := p₀ ≫ snd G G
  let x₁ := p₁ ≫ fst G G
  let y₁ := p₁ ≫ snd G G
  have hx : Family.PointEq.FamilyPointTransport.transportPoint G f.left g.left e x₀ = x₁ := by
    apply Over.OverMorphism.ext
    have he := U.prescribedDualRelation_lift_target_of_base hU π hk hrigid
      (c ≫ U.prescribedDualPairFst) f g (Category.assoc _ _ _) h
    exact he.symm.trans (congrArg Over.Hom.left (U.prescribedDualPairTarget_fst π hU hk)).symm
  have hy : Family.PointEq.FamilyPointTransport.transportPoint G f.left g.left e y₀ = y₁ := by
    apply Over.OverMorphism.ext
    have he := U.prescribedDualRelation_lift_target_of_base hU π hk hrigid
      (c ≫ U.prescribedDualPairSnd) f g (by
        rw [Category.assoc, U.prescribedDualPairSnd_projection]) h
    exact he.symm.trans (congrArg Over.Hom.left (U.prescribedDualPairTarget_snd π hU hk)).symm
  have hm := Family.PointEq.FamilyPointTransport.transportPoint_mul G f.left g.left e x₀ y₀
  rw [hx, hy] at hm
  have hp₀ : x₀ * y₀ = p₀ ≫ (MonObj.mul : G ⊗ G ⟶ G) :=
    Over.OverMorphism.ext (Family.PointEq.FamilyPointTransport.over_pair_mul_left G f.left p₀)
  rw [hp₀] at hm
  have he := U.prescribedDualRelation_lift_target_of_base hU π hk hrigid
    (c ≫ U.prescribedDualMul) f g (by rw [Category.assoc, U.prescribedDualMul_projection]) h
  apply Over.OverMorphism.ext
  exact he.trans ((congrArg Over.Hom.left hm).trans (Family.PointEq.FamilyPointTransport.over_pair_mul_left G g.left p₁))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
