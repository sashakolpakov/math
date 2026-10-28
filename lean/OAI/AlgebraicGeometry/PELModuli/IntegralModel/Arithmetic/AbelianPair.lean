import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.PrescribedSchemeDescentDenominator
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.DualRelation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.FamilyExtension
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Prescribed.DualQuotient
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.Pair

/-! # Abelian Pair -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.AbelianPair.ArithmeticPELComparison

noncomputable section

/-! Construct the universal abelian family and its dual-cover abelian
family on one actual localization of a number field's ring of integers.
The common-base map and both group comparisons are constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {κ : K →+* ℂ} (B : Base.ArithmeticBaseExtension K κ)
    {s N p : ℕ} [Fact p.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) {V Q : Over B.base}
    [IsReduced V.left] [IsLocallyNoetherian V.left]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]

theorem prescribed_arithmetic_abelian_pair
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N V)
    (hU : U.IsFine) (hrigid : U.PrescribedRigid)
    (π : V ⟶ Q) [IsFinite π.left] [Etale π.left] [Surjective π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source V (3 * s) p).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)
    (hV : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism V.hom) (hQ : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Q.hom)
    (e : (Over.pullback B.generic).obj V ≅ ReferencePrimeFrame.ArithmeticPELComparison.primeFrame B M p)
    (hAFM : ∀ F : Set (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left, F.Finite →
      ∃ W : (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left.Opens, IsAffineOpen W ∧ F ⊆ W)
    (d : (Over.pullback B.generic).obj Q ≅ ReferencePrimeFrame.ArithmeticPELComparison.referenceSpace B M)
    (a : PEL.Iso.PolarizedActionIso
      ((ReferencePrimeFrame.ArithmeticPELComparison.referenceFamily B M).pullback ((Over.pullback B.generic).map π ≫ d.hom)).data
      (U.genericIntegralFamily B iota).forgetAuxiliary.data) :
    ∃ D : Base.ArithmeticBaseExtension B.extension.carrier B.embedding,
      B.denominator ∣ D.denominator ∧ ∃ φ : B.R →+* D.R,
        D.toField.comp φ = (algebraMap B.extension.carrier D.extension.carrier).comp B.toField ∧
        Nonempty (U.PrescribedAbelianPair hU π hk (Spec.map (CommRingCat.ofHom φ))) := by
  obtain ⟨_, _, _, n, hn, hBn, φ₀, hφ₀, Y₀, q₀, b₀, hY₀, hc₀, he₀, _⟩ :=
    DualRelation.ArithmeticPELComparison.prescribed_dual_arithmetic_relation_model B M U hU π hk hrigid hV hQ d a
      B.denominator B.denominator_ne_zero
  obtain ⟨D, hnD, φ, hφ, A, qA, hcartA, hsA, hpA, hgA, _, _, _, _, hkA⟩ :=
    PrescribedSchemeDescentDenominator.ArithmeticPELComparison.prescribed_family_arithmetic_scheme_descends_with_denominator B M U hU hrigid π hk e hAFM n hn
  obtain ⟨Y, qD, bD, _, hcartD, heD⟩ := FamilyExtension.arithmetic_family_model_extend B D n hn hnD φ₀ hφ₀ φ hφ
    U.prescribedDualProjection π (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)
    (U.prescribedDualOverlapTarget hU π hk) Y₀ q₀ b₀ hY₀ hc₀ he₀
  let b := Spec.map (CommRingCat.ofHom φ)
  let F := Over.pullback b
  let C : Over (F.obj Q).left := Over.mk bD.left
  have hcartC : IsPullback (F.map U.prescribedDualProjection).left qD.left (F.map π).left C.hom :=
    hcartD.map (Over.forget D.base)
  have heC : (F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left ≫ qD.left =
      (F.map (U.prescribedDualOverlapTarget hU π hk)).left ≫ qD.left := congrArg Over.Hom.left heD
  obtain ⟨hsC, _, hpC, hgC, _, _, _, hkC⟩ := U.prescribed_dual_quotient_geometry hU π hk b C qD.left hcartC heC
  have : Smooth A.hom := hsA
  have : IsProper A.hom := hpA
  have : GeometricallyConnected A.hom := hgA
  have : Smooth C.hom := hsC
  have : IsProper C.hom := hpC
  have : GeometricallyConnected C.hom := hgC
  exact ⟨D, hBn.trans hnD, φ, hφ,
    U.prescribed_abelian_pair_of_quotients hU π hk hrigid b A C qA qD.left hcartA hcartC hkA hkC⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.AbelianPair.ArithmeticPELComparison
