import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.SchemeDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChangedDescentAffineCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChangedPolarizedTotalSpace
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComplexCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.BaseChangeComparisons

/-! # Family Complex Cover -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.FamilyComplexCover.ArithmeticPELComparison

noncomputable section

/-! The actual arithmetic universal-family descent relation admits a
finite invariant affine cover on its literal complex scalar change.
This uses the given reference comparison and the proved affine geometry
of the reference, together with the actual polarization embedding. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {κ : K →+* ℂ} (B : Base.ArithmeticBaseExtension K κ)
    {s N p : ℕ} [Fact p.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) {V Q : Over B.base}
    [IsReduced V.left] [IsLocallyNoetherian V.left] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]

theorem prescribed_family_complex_invariant_affine_cover
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N V)
    (hU : U.IsFine) (hrigid : U.PrescribedRigid)
    (π : V ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source V (3 * s) p).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)
    (e : (Over.pullback B.generic).obj V ≅ ReferencePrimeFrame.ArithmeticPELComparison.primeFrame B M p)
    (hAFM : ∀ F : Set (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left, F.Finite →
      ∃ W : (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left.Opens, IsAffineOpen W ∧ F ⊆ W) :
    let b := Spec.map (CommRingCat.ofHom (B.embedding.comp B.toField))
    ∃ (I : Type) (_ : Finite I) (W : I → ((Over.pullback b).obj U.prescribedTotalSpace).left.Opens),
      (∀ i, IsAffineOpen (W i)) ∧
      (∀ i, ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left ⁻¹ᵁ W i =
        ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left ⁻¹ᵁ W i) ∧ iSup W = ⊤ := by
  let φ := B.embedding.comp B.toField
  let b := Spec.map (CommRingCat.ofHom φ)
  let VC := (Over.pullback b).obj V
  have hb : b = B.complexPoint := Spec.map_comp (CommRingCat.ofHom B.toField)
    (CommRingCat.ofHom B.embedding)
  let d : VC ≅ (Over.pullback B.complexPoint).obj V := Group.BaseChangeComparisons.GroupBaseChange.congrIso V b B.complexPoint hb
  obtain ⟨q, hqf, _, _⟩ := ComplexCover.ArithmeticPELComparison.complex_reference_cover B M e
  have : IsFinite q.left := hqf
  have : IsIso d.hom.left := ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso d).isIso_hom
  have hAF := Affine.NeighborhoodPullback.finite_set_affine_neighborhood_of_affine (d.hom.left ≫ q.left) hAFM
  have : LocallyOfFiniteType VC.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd V.hom b))
  have : IsLocallyNoetherian VC.left := LocallyOfFiniteType.isLocallyNoetherian VC.hom
  have hAFtotal := ChangedPolarizedTotalSpace.baseChanged_polarized_totalSpace_affine_neighborhoods φ V hAF
    U.forgetAuxiliary.data.polarized
  have : QuasiCompact U.prescribedTotalSpace.hom :=
    inferInstanceAs (QuasiCompact (U.forgetAuxiliary.data.polarized.abelian.scheme.hom ≫ V.hom))
  have : QuasiCompact ((Over.pullback b).obj U.prescribedTotalSpace).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd U.prescribedTotalSpace.hom b))
  have : CompactSpace ((Over.pullback b).obj U.prescribedTotalSpace).left :=
    QuasiCompact.compactSpace_of_compactSpace ((Over.pullback b).obj U.prescribedTotalSpace).hom
  let a := U.prescribedProjection
  let t := U.prescribedOverlapTarget hU π hk
  have ht : t ≫ a = DescentCocycleChange.DescentCocycle.base π a := U.prescribedOverlapTarget_base hU π hk
  let er := DescentCocycleChange.DescentCocycle.equivalenceRelation π a t ht
    (U.prescribedOverlapTarget_normalized hU π hk hrigid)
    (U.prescribedOverlapTarget_cocycle hU π hk hrigid)
  exact ChangedDescentAffineCover.baseChanged_descent_finite_invariant_affine_cover b π a (DescentCocycleChange.DescentCocycle.base π a)
    (DescentCocycleChange.DescentCocycle.source π a) t (IsPullback.of_hasPullback (a ≫ π) π).flip ht er hAFtotal

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.FamilyComplexCover.ArithmeticPELComparison
