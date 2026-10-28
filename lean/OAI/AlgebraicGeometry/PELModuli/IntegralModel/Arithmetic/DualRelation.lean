import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GenericDualRelation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldCartesianFamilyRelation

/-! # Dual Relation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.DualRelation.ArithmeticPELComparison

noncomputable section

/-! Construct an arithmetic scheme model of the actual universal dual,
retaining the given generic dual and the actual arithmetic family cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {κ : K →+* ℂ} (B : Base.ArithmeticBaseExtension K κ)
    {s N p : ℕ} [NeZero p] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) {V Q : Over B.base}
    [IsReduced V.left] [IsLocallyNoetherian V.left]

theorem prescribed_dual_arithmetic_relation_model
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N V) (hU : U.IsFine)
    (π : V ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source V (3 * s) p).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left) (hrigid : U.PrescribedRigid)
    (hV : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism V.hom) (hQ : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Q.hom)
    (d : (Over.pullback B.generic).obj Q ≅ ReferencePrimeFrame.ArithmeticPELComparison.referenceSpace B M)
    (a : PEL.Iso.PolarizedActionIso
      ((ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M).pullback ((Over.pullback B.generic).map π ≫ d.hom)).data
      (U.genericIntegralFamily B iota).forgetAuxiliary.data)
    (N₀ : ℕ) (hN₀ : N₀ ≠ 0) :
    let G := Over.pullback B.generic
    let Dg := (ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M).data.polarized.dual.abelian.pullback d.hom.left
    let Yg := (Over.map (G.obj Q).hom).obj Dg.scheme
    ∃ qg : G.obj U.prescribedDualTotalSpace ⟶ Yg,
      IsPullback (G.map U.prescribedDualProjection) qg (G.map π)
        (Over.homMk Dg.scheme.hom : Yg ⟶ G.obj Q) ∧
      G.map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection) ≫ qg =
        G.map (U.prescribedDualOverlapTarget hU π hk) ≫ qg ∧
    ∃ (n : ℕ) (hn : n ≠ 0), N₀ ∣ n ∧
      let D := B.withDenominator n hn
      ∃ φ : B.R →+* D.R, D.toField.comp φ = B.toField ∧
        let F := Over.pullback (Spec.map (CommRingCat.ofHom φ))
        ∃ (Y : Over D.base) (q : F.obj U.prescribedDualTotalSpace ⟶ Y) (b : Y ⟶ F.obj Q),
          ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom ∧
          IsPullback (F.map U.prescribedDualProjection) q (F.map π) b ∧
          F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection) ≫ q =
            F.map (U.prescribedDualOverlapTarget hU π hk) ≫ q ∧
          ∃ ec : F ⋙ Over.pullback D.generic ≅ G,
          ∃ ey : (Over.pullback D.generic).obj Y ≅ Yg,
            (Over.pullback D.generic).map q ≫ ey.hom = (ec.app U.prescribedDualTotalSpace).hom ≫ qg ∧
            (Over.pullback D.generic).map b ≫ (ec.app Q).hom =
              ey.hom ≫ (Over.homMk Dg.scheme.hom : Yg ⟶ G.obj Q) := by
  let : Algebra B.R B.extension.carrier := B.toField.toAlgebra
  have hAlg : algebraMap B.R B.extension.carrier = B.toField := rfl
  have : LocallyOfFinitePresentation V.hom := hV.1
  have : QuasiCompact V.hom := hV.2.1
  have : QuasiSeparated V.hom := hV.2.2
  have hW : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism U.prescribedDualTotalSpace.hom := by
    change ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism
      (U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom ≫ V.hom)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have : LocallyOfFinitePresentation U.prescribedDualTotalSpace.hom := hW.1
  have : QuasiCompact U.prescribedDualTotalSpace.hom := hW.2.1
  have : QuasiSeparated U.prescribedDualTotalSpace.hom := hW.2.2
  have hZ : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (U.prescribedDualOverlap π).hom := by
    rw [← (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection).w]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨hY, q, hc, he⟩ := GenericDualRelation.ArithmeticPELComparison.generic_dual_family_cartesian_relation B M U hU π hk hrigid hQ d a
  refine ⟨q, hc, he, ?_⟩
  exact FieldCartesianFamilyRelation.numberField_cartesian_family_relation_model B hAlg hZ hW hV hQ
    (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection) (U.prescribedDualOverlapTarget hU π hk)
    U.prescribedDualProjection π _ hY q _ hc he N₀ hN₀

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.DualRelation.ArithmeticPELComparison
