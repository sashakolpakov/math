import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Prescribed.DualScalarGroupOperations
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Prescribed.DualZeroDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Prescribed.DualInverseDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Prescribed.DualMultiplicationDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.GroupPair

/-! # Dual Group Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Construct the commutative group structure on the actual arithmetic
dual family quotient, with the actual covering-family group comparison. -/

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
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left] [Surjective π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribed_dual_group_descends (hrigid : U.PrescribedRigid)
    {S : Scheme.{0}} (b : S ⟶ Spec (.of R))
    (A : Over ((Over.pullback b).obj Q).left)
    (q : ((Over.pullback b).obj U.prescribedDualTotalSpace).left ⟶ A.left)
    [Flat q] [Surjective q] [LocallyOfFinitePresentation q]
    (hcart : IsPullback ((Over.pullback b).map U.prescribedDualProjection).left q
      ((Over.pullback b).map π).left A.hom)
    (hq : IsKernelPair q ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left
      ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left) :
    ∃ gA : GrpObj A, (letI := gA; IsCommMonObj A) ∧
      ∃ e : (Relative.ScalarFunctor.relativeScalarFunctor b X).obj U.forgetAuxiliary.data.polarized.dual.abelian.scheme ≅
        (Over.pullback ((Over.pullback b).map π).left).obj A,
        e.hom.left ≫ pullback.fst A.hom ((Over.pullback b).map π).left = q ∧
          (letI := gA; IsMonHom e.hom) := by
  let F := Over.pullback b
  let H := Relative.ScalarFunctor.relativeScalarFunctor b X
  let G := U.forgetAuxiliary.data.polarized.dual.abelian.scheme
  let u := (F.map π).left
  have : Flat u := MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Flat π.left))
  have : Surjective u := MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Surjective π.left))
  have : LocallyOfFinitePresentation u := MorphismProperty.of_isPullback
    (Specialization.base_change_square b π) (inferInstanceAs (LocallyOfFinitePresentation π.left))
  let e : H.obj G ≅ (Over.pullback u).obj A :=
    Over.isoMk hcart.flip.isoPullback hcart.flip.isoPullback_hom_snd
  have he : e.hom.left ≫ pullback.fst A.hom u = q := hcart.flip.isoPullback_hom_fst
  obtain ⟨z, hz, _⟩ := U.prescribed_dual_zero_descends hU π hk hrigid b A q hcart hq
  obtain ⟨d, hd, _⟩ := U.prescribed_dual_inverse_descends hU π hk hrigid b A q hcart hq
  obtain ⟨q₂, h₁, h₂, _, _, _, _, m, hm, _⟩ :=
    U.prescribed_dual_multiplication_descends hU π hk hrigid b A q hcart hq
  let qp := (Functor.LaxMonoidal.μ H G G).left ≫ q₂
  have hμ₁ : (Functor.LaxMonoidal.μ H G G).left ≫ (F.map U.prescribedDualPairFst).left =
      (fst (H.obj G) (H.obj G)).left :=
    congrArg Over.Hom.left (Functor.Monoidal.μ_fst H G G)
  have hμ₂ : (Functor.LaxMonoidal.μ H G G).left ≫ (F.map U.prescribedDualPairSnd).left =
      (snd (H.obj G) (H.obj G)).left :=
    congrArg Over.Hom.left (Functor.Monoidal.μ_snd H G G)
  have hp₁ : qp ≫ (fst A A).left = (fst (H.obj G) (H.obj G)).left ≫ q := by
    change (_ ≫ q₂) ≫ _ = _
    rw [Category.assoc, h₁, ← Category.assoc, hμ₁]
  have hp₂ : qp ≫ (snd A A).left = (snd (H.obj G) (H.obj G)).left ≫ q := by
    change (_ ≫ q₂) ≫ _ = _
    rw [Category.assoc, h₂, ← Category.assoc, hμ₂]
  have hz' : u ≫ z.left = (MonObj.one : 𝟙_ (Over ((F.obj X).left)) ⟶ H.obj G).left ≫ q := by
    rw [U.prescribed_dual_scalar_one b]
    exact hz
  have hd' : q ≫ d.left = (GrpObj.inv : H.obj G ⟶ H.obj G).left ≫ q := by
    rw [U.prescribed_dual_scalar_inverse b]
    exact hd
  have hm' : qp ≫ m.left = (MonObj.mul : H.obj G ⊗ H.obj G ⟶ H.obj G).left ≫ q := by
    rw [U.prescribed_dual_scalar_mul b]
    change (_ ≫ q₂) ≫ _ = _
    rw [Category.assoc, hm, Category.assoc]
  obtain ⟨gA, hgA, heG⟩ := Cartesian.GroupPair.commutative_group_descends_from_cartesian_operations u (H.obj G) A
    e q he qp hp₁ hp₂ z m d hz' hm' hd'
  exact ⟨gA, hgA, e, he, heG⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
