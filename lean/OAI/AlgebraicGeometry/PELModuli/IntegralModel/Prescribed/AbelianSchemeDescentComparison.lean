import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Prescribed.DualGroupDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.EtaleRelativeDimension

/-! # Abelian Scheme Descent Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The constructed abelian scheme retains the exact projection
of its group comparison onto the original quotient cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left] [Surjective π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribed_dual_abelian_scheme_descends_with_comparison (hrigid : U.PrescribedRigid)
    {S : Scheme.{0}} (b : S ⟶ Spec (.of R))
    (A : Over ((Over.pullback b).obj Q).left)
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (q : ((Over.pullback b).obj U.prescribedDualTotalSpace).left ⟶ A.left)
    [Flat q] [Surjective q] [LocallyOfFinitePresentation q]
    (hcart : IsPullback ((Over.pullback b).map U.prescribedDualProjection).left q
      ((Over.pullback b).map π).left A.hom)
    (hq : IsKernelPair q ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left
      ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left) :
    ∃ B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) ((Over.pullback b).obj Q).left, ∃ hB : B.scheme = A,
      ∃ e : (Relative.ScalarFunctor.relativeScalarFunctor b X).obj U.forgetAuxiliary.data.polarized.dual.abelian.scheme ≅
        (Over.pullback ((Over.pullback b).map π).left).obj B.scheme,
        e.hom.left ≫ pullback.fst B.scheme.hom ((Over.pullback b).map π).left ≫
          eqToHom (congrArg Over.left hB) = q ∧ IsMonHom e.hom := by
  let F := Over.pullback b
  have : Etale (F.map π).left := MorphismProperty.of_isPullback (Specialization.base_change_square b π)
    (inferInstanceAs (Etale π.left))
  have : Etale q := MorphismProperty.of_isPullback hcart (inferInstanceAs (Etale (F.map π).left))
  have hd : SmoothOfRelativeDimension (3 * s) (F.map U.prescribedDualProjection).left := by
    have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension (3 * s)) :=
      smoothOfRelativeDimension_isStableUnderBaseChange (3 * s)
    exact MorphismProperty.of_isPullback (Specialization.base_change_square b U.prescribedDualProjection)
      (inferInstanceAs (SmoothOfRelativeDimension (3 * s) U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom))
  have : SmoothOfRelativeDimension (3 * s) (q ≫ A.hom) := by
    rw [← hcart.w]
    exact inferInstanceAs (SmoothOfRelativeDimension (3 * s + 0)
      ((F.map U.prescribedDualProjection).left ≫ (F.map π).left))
  have hdim : SmoothOfRelativeDimension (3 * s) A.hom :=
    EtaleRelativeDimension.DimensionSupport.smooth_relative_dimension_of_etale_cover q A.hom (3 * s)
  obtain ⟨gA, hc, e, heq, he⟩ := U.prescribed_dual_group_descends hU π hk hrigid b A q hcart hq
  let := gA
  let B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) ((F.obj Q).left) := {
    scheme := A
    group := gA
    commutative := hc
    proper := inferInstance
    smoothDimension := hdim
    connected := inferInstance }
  exact ⟨B, rfl, e, by simpa only [eqToHom_refl, Category.comp_id] using heq, he⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
