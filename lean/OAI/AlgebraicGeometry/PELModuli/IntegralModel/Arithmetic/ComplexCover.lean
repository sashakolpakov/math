import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ReferencePrimeFrame
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.PELFrameGeometry
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.BaseChangeComparisons
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ReducedComplexPEL

/-! # Complex Cover -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComplexCover

noncomputable section

/-! The actual generic reference comparison gives a finite etale
surjective map from the arithmetic parameter's complex fiber to the
given reduced complex PEL reference. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace ArithmeticPELComparison
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {κ : K →+* ℂ} (B : Base.ArithmeticBaseExtension K κ)
    {s N p : ℕ} [Fact p.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) {V : Over B.base}

theorem complex_reference_cover
    (e : (Over.pullback B.generic).obj V ≅ ReferencePrimeFrame.ArithmeticPELComparison.primeFrame B M p) :
    ∃ q : (Over.pullback B.complexPoint).obj V ⟶ Reduced.ReducedComplexPEL.reducedComplexPEL M κ,
      IsFinite q.left ∧ Etale q.left ∧ Surjective q.left := by
  let c := Spec.map (CommRingCat.ofHom B.embedding)
  have hc : c ≫ B.fieldExtension = Spec.map (CommRingCat.ofHom κ) := by
    change Spec.map (CommRingCat.ofHom B.embedding) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K B.extension.carrier)) = _
    rw [← Spec.map_comp]
    exact congrArg (fun r : K →+* ℂ => Spec.map (CommRingCat.ofHom r)) B.embedding_extends
  let eV : (Over.pullback B.complexPoint).obj V ≅ (Over.pullback c).obj (ReferencePrimeFrame.ArithmeticPELComparison.primeFrame B M p) :=
    (Over.pullbackComp c B.generic).app V ≪≫ (Over.pullback c).mapIso e
  let eM : (Over.pullback c).obj (ReferencePrimeFrame.ArithmeticPELComparison.referenceSpace B M) ≅ Reduced.ReducedComplexPEL.reducedComplexPEL M κ :=
    (Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso B.fieldExtension c (Spec.map (CommRingCat.ofHom κ)) hc).app
      (Reduction.reduction M.space)
  let f := IntegralPEL.FrameExistence.IntegralPELFrame.forget (ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M) (ReferencePrimeFrame.ArithmeticPELComparison.primeUnit B M p)
  obtain ⟨hf, ht, hs⟩ := IntegralPEL.PELFrameGeometry.IntegralPELFrame.finite_etale_surjective
    (ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M) (ReferencePrimeFrame.ArithmeticPELComparison.primeUnit B M p) (Fact.out : p.Prime)
  let f' := (Over.pullback c).map f
  have : IsFinite f'.left := MorphismProperty.of_isPullback (Specialization.base_change_square c f) hf
  have : Etale f'.left := MorphismProperty.of_isPullback (Specialization.base_change_square c f) ht
  have : Surjective f'.left := MorphismProperty.of_isPullback (Specialization.base_change_square c f) hs
  have : IsIso eV.hom.left := ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso eV).isIso_hom
  have : IsIso eM.hom.left := ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso eM).isIso_hom
  have : IsFinite eV.hom.left := inferInstance
  have : IsFinite eM.hom.left := inferInstance
  have : Etale eV.hom.left := inferInstance
  have : Etale eM.hom.left := inferInstance
  have : Surjective eV.hom.left := inferInstance
  have : Surjective eM.hom.left := inferInstance
  exact ⟨eV.hom ≫ f' ≫ eM.hom,
    inferInstanceAs (IsFinite (eV.hom.left ≫ f'.left ≫ eM.hom.left)),
    inferInstanceAs (Etale (eV.hom.left ≫ f'.left ≫ eM.hom.left)),
    inferInstanceAs (Surjective (eV.hom.left ≫ f'.left ≫ eM.hom.left))⟩

end ArithmeticPELComparison

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComplexCover
