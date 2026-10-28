import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.AdditiveComplexExtension
import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechResolution

/-! # Cech Resolution -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CechResolution

noncomputable section

/-! The actual total Čech resolution maps from the preserved integer algebraic complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {ι : Type} (U : ι → X.left.Opens)

def algebraicCechTotalComplex : CochainComplex (HypercohomologyForget.AdditiveZariskiSheaves X) ℕ :=
  (Sheaf.CechAugmentation.sheafCechBicomplex U (AdditiveComplexExtension.algebraicAdditiveSheafComplex X)).total (.up ℕ)

def algebraicCechTotalComplexInt : CochainComplex (HypercohomologyForget.AdditiveZariskiSheaves X) ℤ :=
  (algebraicCechTotalComplex X U).extend (ComplexShape.embeddingUpIntGE 0)

instance algebraicCechTotalComplexInt_nonnegative :
    (algebraicCechTotalComplexInt X U).IsStrictlyGE 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyGE
    ((algebraicCechTotalComplex X U).extend (ComplexShape.embeddingUpIntGE 0)) 0)

def algebraicCechResolutionMap :
    HypercohomologyForget.algebraicAdditiveSheafComplexInt X ⟶ algebraicCechTotalComplexInt X U :=
  (AdditiveComplexExtension.algebraicAdditiveComplexExtensionIso X).hom ≫
    HomologicalComplex.extendMap
      (Sheaf.CechAugmentation.sheafCechResolutionEdge U (AdditiveComplexExtension.algebraicAdditiveSheafComplex X))
      (ComplexShape.embeddingUpIntGE 0)

theorem algebraicCechResolutionMap_quasiIso (hU : ⨆ i, U i = ⊤) :
    QuasiIso (algebraicCechResolutionMap X U) := by
  have : QuasiIso (Sheaf.CechAugmentation.sheafCechResolutionEdge U (AdditiveComplexExtension.algebraicAdditiveSheafComplex X)) :=
    Sheaf.CechResolution.sheafCechResolutionEdge_quasiIso U hU (AdditiveComplexExtension.algebraicAdditiveSheafComplex X)
  have : QuasiIso (HomologicalComplex.extendMap
      (Sheaf.CechAugmentation.sheafCechResolutionEdge U (AdditiveComplexExtension.algebraicAdditiveSheafComplex X))
      (ComplexShape.embeddingUpIntGE 0)) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).mpr inferInstance
  have : QuasiIso (AdditiveComplexExtension.algebraicAdditiveComplexExtensionIso X).hom := inferInstance
  exact inferInstanceAs (QuasiIso ((AdditiveComplexExtension.algebraicAdditiveComplexExtensionIso X).hom ≫
    HomologicalComplex.extendMap
      (Sheaf.CechAugmentation.sheafCechResolutionEdge U (AdditiveComplexExtension.algebraicAdditiveSheafComplex X))
      (ComplexShape.embeddingUpIntGE 0)))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CechResolution
