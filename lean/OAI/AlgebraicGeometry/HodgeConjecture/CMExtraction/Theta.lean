import OAI.Analysis.HodgeTheory.Decomposition.Constructions
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ComparisonIntrinsicClass

/-! # Theta -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Theta

noncomputable section

/-! Instantiate the native Hodge construction with the proved full HodgeDecomposition
theorem. The theta and comparison classes retain their geometric meanings. -/

section

theorem verifiedHodgeDecomposition : Mem.HodgeDecompositionInput := Analysis.HodgeTheory.Decomposition.Constructions.hodge_decomposition_and_filtration

end

namespace Intrinsic

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def verifiedNativeH1 (hg : D.pel.HasIntegralModelGeometry) : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure D.pel.H1 :=
  Intrinsic.Base.nativeH1 D verifiedHodgeDecomposition hg

theorem verifiedNativeH1_eq (hHodgeDecomposition : Mem.HodgeDecompositionInput) (hg : D.pel.HasIntegralModelGeometry) :
    verifiedNativeH1 D hg = Intrinsic.Base.nativeH1 D hHodgeDecomposition hg := rfl

theorem nativeThetaClass_verified_holomorphic (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA) (φ : D.sphericalInputs) :
    Intrinsic.ThetaClass.nativeThetaClass D hg Θ φ ∈ (verifiedNativeH1 D hg).holomorphic :=
  Intrinsic.ThetaClass.nativeThetaClass_holomorphic D verifiedHodgeDecomposition hg Θ φ

theorem native_verified_holomorphic_complex_image (hg : D.pel.HasIntegralModelGeometry)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation D.pel.complexAlbanese.X.left D.pel.complexAlbanese.X.hom) :
    (verifiedNativeH1 D hg).holomorphic.map (ComparisonBetti.Intrinsic.nativeBettiComplexification D hg).toLinearMap =
      (ComparisonIntrinsicClass.Intrinsic.nativeAlbanesePresentation D hg P).pureBettiSubspace 1 0 :=
  ComparisonIntrinsicClass.Intrinsic.native_holomorphic_complex_image D verifiedHodgeDecomposition hg P

end Intrinsic

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Theta
