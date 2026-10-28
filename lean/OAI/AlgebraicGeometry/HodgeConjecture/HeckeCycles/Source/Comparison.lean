import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ComparisonIntrinsicClass
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Comap
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel

/-! # Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Comparison.CM

noncomputable section

/-! The source GeometricTheta Hodge structure and the ordinary comparison model's
Hodge structure agree on their actual common rational Albanese H1.
The identification follows from the identity algebraic pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ComparisonIntrinsicClass.Intrinsic

theorem antiholomorphic_of_holomorphic
    {U : Type*} [AddCommGroup U] [Module ℚ U]
    (H K : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (h : H.holomorphic = K.holomorphic) :
    H.antiholomorphic = K.antiholomorphic := by
  ext x
  have h₁ := H.conjugate_mem (ComplexMultiplication.WeightOne.CM.coefficientConjugation U x)
  have h₂ := K.conjugate_mem (ComplexMultiplication.WeightOne.CM.coefficientConjugation U x)
  rw [ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive, h] at h₁
  rw [ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive] at h₂
  exact h₁.trans h₂.symm

theorem hom_subspace_of_holomorphic
    {U : Type*} [AddCommGroup U] [Module ℚ U]
    (H K : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (h : H.holomorphic = K.holomorphic) :
    ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H = ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace K K := by
  have ha := antiholomorphic_of_holomorphic H K h
  ext f
  change ((∀ x ∈ H.holomorphic, f x ∈ H.holomorphic) ∧
    ∀ x ∈ H.antiholomorphic, f x ∈ H.antiholomorphic) ↔
    ((∀ x ∈ K.holomorphic, f x ∈ K.holomorphic) ∧
    ∀ x ∈ K.antiholomorphic, f x ∈ K.antiholomorphic)
  rw [h, ha]

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q)
  (hcop : Nat.Coprime q D.pel.denominator)

local notation "AM" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel D.pel hg j hcop
local notation "H" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Comap.CM.hodge AM D.pel.complexEmbedding

theorem holomorphic (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput) :
    (CMExtraction.Intrinsic.Base.nativeH1 D hHodgeDecomposition hg).holomorphic = (H).holomorphic := by
  let V := Constructed.Comap.CM.variety AM D.pel.complexEmbedding
  have h := CMExtraction.Intrinsic.ProjectivePullback.native_projective_pullback_isHodgeMap D hHodgeDecomposition hg V.presentation
    (𝟙 D.pel.complexAlbanese.X)
  have he : PELModuli.IntegralModel.Product.bettiPullbackQ (𝟙 D.pel.complexAlbanese.X) 1 = LinearMap.id :=
    congrArg ModuleCat.Hom.hom
      ((Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℚ ℚ) 1).map_id (Opposite.op D.pel.complexAlbanese.X))
  have hi : ComplexMultiplication.WeightOne.CM.IsHodgeMap (CMExtraction.Mem.canonicalH1 hHodgeDecomposition V.presentation)
      (CMExtraction.Intrinsic.Base.nativeH1 D hHodgeDecomposition hg) LinearMap.id := he ▸ h
  have hh := CMExtraction.ComparisonIntrinsicClass.holomorphic_eq_of_identity_hodge _ _ hi
  exact hh.symm.trans (CMExtraction.Naturality.canonicalH1_integral_holomorphic hHodgeDecomposition V)

theorem antiholomorphic (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput) :
    (CMExtraction.Intrinsic.Base.nativeH1 D hHodgeDecomposition hg).antiholomorphic = (H).antiholomorphic :=
  antiholomorphic_of_holomorphic (CMExtraction.Intrinsic.Base.nativeH1 D hHodgeDecomposition hg) H (CM.holomorphic D hg j hcop hHodgeDecomposition)

theorem hom_subspace (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput) :
    ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace (CMExtraction.Intrinsic.Base.nativeH1 D hHodgeDecomposition hg) (CMExtraction.Intrinsic.Base.nativeH1 D hHodgeDecomposition hg) = ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H :=
  hom_subspace_of_holomorphic (CMExtraction.Intrinsic.Base.nativeH1 D hHodgeDecomposition hg) H (CM.holomorphic D hg j hcop hHodgeDecomposition)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Comparison.CM
