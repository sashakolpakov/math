import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComplexCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.FiniteAffineCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.RigidityScalarChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.FineBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.NeighborhoodPullback
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleReduced

/-! # Complex Affine Cover -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComplexAffineCover.ArithmeticPELComparison

noncomputable section

/-! The actual compared arithmetic parameter has a finite invariant
affine cover on its complex fiber, ready for finite coefficient spreading. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {κ : K →+* ℂ} (B : Base.ArithmeticBaseExtension K κ)
    {s N p : ℕ} [Fact p.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) {V : Over B.base}
    [QuasiCompact V.hom] [IsSeparated V.hom]

theorem compared_parameter_complex_affine_cover
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N V)
    (hU : U.IsFine) (hrigid : U.PrescribedRigid)
    (e : (Over.pullback B.generic).obj V ≅ ReferencePrimeFrame.ArithmeticPELComparison.primeFrame B M p)
    (hredM : IsReduced (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left)
    (hAFM : ∀ F : Set (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left, F.Finite →
      ∃ W : (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left.Opens, IsAffineOpen W ∧ F ⊆ W) :
    let φ := B.embedding.comp B.toField
    let VC := (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj V
    let UC := U.baseChange φ
    ∃ hred : IsReduced VC.left, let _ : IsReduced VC.left := hred
      ∃ (I : Type) (_ : Finite I) (W : I → VC.left.Opens),
        (∀ i, IsAffineOpen (W i)) ∧
        (∀ i, (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source VC (3 * s) p).left ⁻¹ᵁ W i =
          (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target UC (IntegralAdded.FineBaseChange.integralAddedPEL_fine_baseChange U hU φ)).left ⁻¹ᵁ W i) ∧
        iSup W = ⊤ := by
  let φ := B.embedding.comp B.toField
  let b := Spec.map (CommRingCat.ofHom φ)
  let VC := (Over.pullback b).obj V
  let UC := U.baseChange φ
  have hb : b = B.complexPoint := by
    change Spec.map (CommRingCat.ofHom (B.embedding.comp B.toField)) =
      Spec.map (CommRingCat.ofHom B.embedding) ≫ Spec.map (CommRingCat.ofHom B.toField)
    exact Spec.map_comp (CommRingCat.ofHom B.toField) (CommRingCat.ofHom B.embedding)
  let d : VC ≅ (Over.pullback B.complexPoint).obj V := Group.BaseChangeComparisons.GroupBaseChange.congrIso V b B.complexPoint hb
  obtain ⟨q, hqf, hqt, _⟩ := ComplexCover.ArithmeticPELComparison.complex_reference_cover B M e
  have : IsFinite q.left := hqf
  have : Etale q.left := hqt
  have : IsIso d.hom.left := ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso d).isIso_hom
  let q' := d.hom.left ≫ q.left
  have : IsReduced (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left := hredM
  have hred : IsReduced VC.left := IntegralModel.Finite.EtaleReduced.finite_etale_isReduced q'
  have : IsReduced VC.left := hred
  have : QuasiCompact VC.hom := inferInstanceAs (QuasiCompact (pullback.snd V.hom b))
  have : IsSeparated VC.hom := inferInstanceAs (IsSeparated (pullback.snd V.hom b))
  have : CompactSpace VC.left := QuasiCompact.compactSpace_of_compactSpace VC.hom
  have : VC.left.IsSeparated := ⟨by rw [← terminal.comp_from VC.hom]; infer_instance⟩
  exact ⟨hred, IntegralAuxiliary.FiniteAffineCover.IntegralAuxiliaryAction.exists_finite_invariant_affine_cover UC
    (IntegralAdded.FineBaseChange.integralAddedPEL_fine_baseChange U hU φ)
    (IntegralPrescribed.RigidityScalarChange.integralAddedPEL_prescribedRigid_baseChange U hrigid φ)
    (Affine.NeighborhoodPullback.finite_set_affine_neighborhood_of_affine q' hAFM)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComplexAffineCover.ArithmeticPELComparison
