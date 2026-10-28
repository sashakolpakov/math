import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GenericDualDiagram
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.ScalarReference

/-! # Generic Dual Relation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GenericDualRelation

noncomputable section

/-! The actual ReferenceFamily universal dual supplies a generic cartesian family
diagram which coequalizes the literal arithmetic prescribed dual relation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace ArithmeticPELComparison
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {κ : K →+* ℂ} (B : Base.ArithmeticBaseExtension K κ)
    {s N p : ℕ} [NeZero p] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) {V Q : Over B.base}
    [IsReduced V.left] [IsLocallyNoetherian V.left]

theorem generic_dual_family_cartesian_relation
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N V) (hU : U.IsFine)
    (π : V ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source V (3 * s) p).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left) (hrigid : U.PrescribedRigid)
    (hQ : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Q.hom)
    (d : (Over.pullback B.generic).obj Q ≅ ReferencePrimeFrame.ArithmeticPELComparison.referenceSpace B M)
    (a : PEL.Iso.PolarizedActionIso
      ((ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M).pullback ((Over.pullback B.generic).map π ≫ d.hom)).data
      (U.genericIntegralFamily B iota).forgetAuxiliary.data) :
    let F := Over.pullback B.generic
    let D := (ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M).data.polarized.dual.abelian.pullback d.hom.left
    let Y := (Over.map (F.obj Q).hom).obj D.scheme
    ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom ∧
      ∃ q : F.obj U.prescribedDualTotalSpace ⟶ Y,
        IsPullback (F.map U.prescribedDualProjection) q (F.map π)
          (Over.homMk D.scheme.hom : Y ⟶ F.obj Q) ∧
        F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection) ≫ q =
          F.map (U.prescribedDualOverlapTarget hU π hk) ≫ q := by
  let F := Over.pullback B.generic
  let A := U.forgetAuxiliary.data.polarized.dual.abelian.scheme
  let C := (ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M).data.pullback d.hom.left
  let D := (ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M).data.polarized.dual.abelian.pullback d.hom.left
  let Y := (Over.map (F.obj Q).hom).obj D.scheme
  let a' : PEL.Iso.PolarizedActionIso (C.pullback (F.map π).left)
      (U.baseChange B.toField).forgetAuxiliary.data :=
    (PEL.Iso.PolarizedActionIso.pullbackComp (ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M).data d.hom.left (F.map π).left).trans a
  let e : (Relative.ScalarFunctor.relativeScalarFunctor B.generic V).obj A ≅ (Over.pullback (F.map π).left).obj D.scheme :=
    Relative.ScalarIntrinsicComparison.relativeScalarNativeComparison B.generic V A ≪≫ a'.polarized.dual.symm
  obtain ⟨q, hq, hc⟩ := OverCartesianFamilyIso.over_cartesian_family_of_iso_with_projection
    (F.map U.prescribedDualProjection) (F.map π) D.scheme e
  have : IsReduced ((Over.pullback (Spec.map (CommRingCat.ofHom B.toField))).obj
      (U.prescribedDualOverlap π)).left :=
    B.genericFiber_isReduced (U.prescribedDualOverlap π)
  have he := U.scalarDualOverlap_reference_coequalizes hU π hk hrigid B.toField C a'
  have heq : F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection) ≫ q =
      F.map (U.prescribedDualOverlapTarget hU π hk) ≫ q := by
    apply Over.OverMorphism.ext
    change (F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left ≫ q.left =
      (F.map (U.prescribedDualOverlapTarget hU π hk)).left ≫ q.left
    rw [hq]
    change (F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left ≫
        ((Relative.ScalarIntrinsicComparison.relativeScalarNativeComparison B.generic V A).hom.left ≫ a'.polarized.dual.inv.left) ≫
          pullback.fst D.scheme.hom (F.map π).left =
      (F.map (U.prescribedDualOverlapTarget hU π hk)).left ≫
        ((Relative.ScalarIntrinsicComparison.relativeScalarNativeComparison B.generic V A).hom.left ≫ a'.polarized.dual.inv.left) ≫
          pullback.fst D.scheme.hom (F.map π).left
    simp only [IntegralAdded.PELId.IntegralAddedPELLevel.scalarDualSourcePoint, IntegralAdded.PELId.IntegralAddedPELLevel.scalarDualTargetPoint,
      PEL.Iso.PolarizedActionIso.referenceDualProjection, Category.assoc] at he ⊢
    exact he
  obtain ⟨hY, _, _⟩ := GenericDualDiagram.ArithmeticPELComparison.generic_dual_family_cartesian_diagram B M U π hQ d a
  exact ⟨hY, q, hc, heq⟩

end ArithmeticPELComparison

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GenericDualRelation
