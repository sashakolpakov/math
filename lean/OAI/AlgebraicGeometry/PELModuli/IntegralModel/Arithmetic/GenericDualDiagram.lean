import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GenericDualComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverCartesianFamilyIso
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Finiteness

/-! # Generic Dual Diagram -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GenericDualDiagram.ArithmeticPELComparison

noncomputable section

/-! The given universal dual supplies an actual finite-presentation
generic family diagram over the arithmetic quotient, with its original cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {κ : K →+* ℂ} (B : Base.ArithmeticBaseExtension K κ)
    {s N p : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) {V Q : Over B.base}

theorem generic_dual_family_cartesian_diagram
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N V)
    (π : V ⟶ Q) (hQ : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Q.hom)
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
          (Over.homMk D.scheme.hom : Y ⟶ F.obj Q) := by
  let F := Over.pullback B.generic
  let D := (ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M).data.polarized.dual.abelian.pullback d.hom.left
  let Y := (Over.map (F.obj Q).hom).obj D.scheme
  have hfQ := Coefficient.Finiteness.Coefficients.baseChange_finitePresentation B.generic Q hQ
  have : LocallyOfFinitePresentation (F.obj Q).hom := hfQ.1
  have : QuasiCompact (F.obj Q).hom := hfQ.2.1
  have : QuasiSeparated (F.obj Q).hom := hfQ.2.2
  have hfY : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom := by
    change ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (D.scheme.hom ≫ (F.obj Q).hom)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨e, _⟩ := GenericDualComparison.ArithmeticPELComparison.generic_dual_family_comparison B M U π d a
  exact ⟨hfY, OverCartesianFamilyIso.over_cartesian_family_of_iso (F.map U.prescribedDualProjection) (F.map π) D.scheme e⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GenericDualDiagram.ArithmeticPELComparison
