import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.Relation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.QuotientOf
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.EtaleRelativeDimension

/-! # Dual Quotient -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The cartesian model of the prescribed dual relation is its actual
finite etale quotient and is smooth proper with connected fibers. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left] [Surjective π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribed_dual_quotient_geometry {S : Scheme.{0}} (b : S ⟶ Spec (.of R))
    (Y : Over ((Over.pullback b).obj Q).left)
    (q : ((Over.pullback b).obj U.prescribedDualTotalSpace).left ⟶ Y.left)
    (hc : IsPullback ((Over.pullback b).map U.prescribedDualProjection).left q
      ((Over.pullback b).map π).left Y.hom)
    (he : ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left ≫ q =
      ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left ≫ q) :
    Smooth Y.hom ∧ SmoothOfRelativeDimension (3 * s) Y.hom ∧
      IsProper Y.hom ∧ GeometricallyConnected Y.hom ∧
      IsFinite q ∧ Etale q ∧ Surjective q ∧
      IsKernelPair q ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left
        ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left := by
  let F := Over.pullback b
  have : IsFinite (F.map π).left := MorphismProperty.of_isPullback (Specialization.base_change_square b π)
    (inferInstanceAs (IsFinite π.left))
  have : Etale (F.map π).left := MorphismProperty.of_isPullback (Specialization.base_change_square b π)
    (inferInstanceAs (Etale π.left))
  have : Surjective (F.map π).left := MorphismProperty.of_isPullback (Specialization.base_change_square b π)
    (inferInstanceAs (Surjective π.left))
  have : IsFinite q := MorphismProperty.of_isPullback hc (inferInstanceAs (IsFinite (F.map π).left))
  have : Etale q := MorphismProperty.of_isPullback hc (inferInstanceAs (Etale (F.map π).left))
  have : Surjective q := MorphismProperty.of_isPullback hc (inferInstanceAs (Surjective (F.map π).left))
  have : Smooth (F.map U.prescribedDualProjection).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b U.prescribedDualProjection)
      (inferInstanceAs (Smooth U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom))
  have : IsProper (F.map U.prescribedDualProjection).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b U.prescribedDualProjection)
      (inferInstanceAs (IsProper U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom))
  have : GeometricallyConnected (F.map U.prescribedDualProjection).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b U.prescribedDualProjection)
      (inferInstanceAs (GeometricallyConnected U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom))
  have hs : Smooth Y.hom := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hc
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have : Smooth Y.hom := hs
  have hd : SmoothOfRelativeDimension (3 * s) (F.map U.prescribedDualProjection).left := by
    have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension (3 * s)) :=
      smoothOfRelativeDimension_isStableUnderBaseChange (3 * s)
    exact MorphismProperty.of_isPullback (Specialization.base_change_square b U.prescribedDualProjection)
      (inferInstanceAs (SmoothOfRelativeDimension (3 * s)
        U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom))
  have : SmoothOfRelativeDimension (3 * s) (q ≫ Y.hom) := by
    rw [← hc.w]
    exact inferInstanceAs (SmoothOfRelativeDimension (3 * s + 0)
      ((F.map U.prescribedDualProjection).left ≫ (F.map π).left))
  have hdim := EtaleRelativeDimension.DimensionSupport.smooth_relative_dimension_of_etale_cover q Y.hom (3 * s)
  have hsource : IsPullback (F.map (DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection)).left
      (F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left (F.map π).left
      (F.map (U.prescribedDualProjection ≫ π)).left :=
    (((IsPullback.of_hasPullback (U.prescribedDualProjection ≫ π) π).flip.map F).map (Over.forget S))
  have hsource' : IsPullback (F.map (DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection)).left
      (F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left (F.map π).left
      ((F.map U.prescribedDualProjection).left ≫ (F.map π).left) := by
    rw [← Over.comp_left, ← F.map_comp]
    exact hsource
  have ht : (F.map (U.prescribedDualOverlapTarget hU π hk)).left ≫
      (F.map U.prescribedDualProjection).left =
        (F.map (DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection)).left :=
    (congrArg Over.Hom.left (F.map_comp _ _)).symm.trans
      (congrArg (fun k => (F.map k).left) (U.prescribedDualOverlapTarget_base hU π hk))
  exact ⟨hs, hdim, Descent.proper_of_faithfully_flat_cartesian hc,
    ArithmeticGeometry.Models.SpreadingOut.GeometricDescent.Construction.geometricallyConnected_of_surjective_cartesian hc.flip,
    inferInstance, inferInstance, inferInstance,
    Family.QuotientOf.kernelPair_of_cartesian_relation _ _ _ _ hc _ _ _ hsource' ht he⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
