import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.FamilyComplexCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.RelationAffineCoverSpecialization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ChangedDescentAffineCover

/-! # Prescribed Scheme Descent Denominator -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.PrescribedSchemeDescentDenominator.ArithmeticPELComparison

noncomputable section

/-! Construct the arithmetic universal abelian-family scheme while
inverting any prescribed nonzero integer. This permits its arithmetic
base to receive the already constructed dual-family model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {κ : K →+* ℂ} (B : Base.ArithmeticBaseExtension K κ)
    {s N p : ℕ} [Fact p.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) {V Q : Over B.base}
    [IsReduced V.left] [IsLocallyNoetherian V.left]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]

theorem prescribed_family_arithmetic_scheme_descends_with_denominator
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N V)
    (hU : U.IsFine) (hrigid : U.PrescribedRigid)
    (π : V ⟶ Q) [IsFinite π.left] [Etale π.left] [Surjective π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source V (3 * s) p).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)
    (e : (Over.pullback B.generic).obj V ≅ ReferencePrimeFrame.ArithmeticPELComparison.primeFrame B M p)
    (hAFM : ∀ F : Set (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left, F.Finite →
      ∃ W : (Reduced.ReducedComplexPEL.reducedComplexPEL M κ).left.Opens, IsAffineOpen W ∧ F ⊆ W)
    (N₀ : ℕ) (hN₀ : N₀ ≠ 0) :
    ∃ D : Base.ArithmeticBaseExtension B.extension.carrier B.embedding,
      N₀ ∣ D.denominator ∧ ∃ φ : B.R →+* D.R,
        D.toField.comp φ = (algebraMap B.extension.carrier D.extension.carrier).comp B.toField ∧
        let b := Spec.map (CommRingCat.ofHom φ)
        ∃ (A : Over ((Over.pullback b).obj Q).left)
          (q : ((Over.pullback b).obj U.prescribedTotalSpace).left ⟶ A.left),
          IsPullback ((Over.pullback b).map U.prescribedProjection).left q
            ((Over.pullback b).map π).left A.hom ∧
          Smooth A.hom ∧ IsProper A.hom ∧ GeometricallyConnected A.hom ∧
          IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧
          IsKernelPair q ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left
            ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left := by
  let φC := B.embedding.comp B.toField
  let : Algebra B.R ℂ := φC.toAlgebra
  obtain ⟨I, hI, W, hW, hInv, hcover⟩ :=
    FamilyComplexCover.ArithmeticPELComparison.prescribed_family_complex_invariant_affine_cover B M U hU hrigid π hk e hAFM
  have : Finite I := hI
  let a := U.prescribedProjection
  let src := DescentCocycleChange.DescentCocycle.source π a
  let t := U.prescribedOverlapTarget hU π hk
  have : Smooth a.left := inferInstanceAs (Smooth U.forgetAuxiliary.data.polarized.abelian.scheme.hom)
  have : IsProper a.left := inferInstanceAs (IsProper U.forgetAuxiliary.data.polarized.abelian.scheme.hom)
  have : GeometricallyConnected a.left :=
    inferInstanceAs (GeometricallyConnected U.forgetAuxiliary.data.polarized.abelian.scheme.hom)
  have hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism U.prescribedTotalSpace.hom := by
    change ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (U.forgetAuxiliary.data.polarized.abelian.scheme.hom ≫ V.hom)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have : LocallyOfFinitePresentation U.prescribedTotalSpace.hom := hX.1
  have : QuasiCompact U.prescribedTotalSpace.hom := hX.2.1
  have : QuasiSeparated U.prescribedTotalSpace.hom := hX.2.2
  have hZ : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (U.prescribedOverlap π).hom := by
    rw [← src.w]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨D, hdiv, φ, hbase, W', hW', hcover', hInv'⟩ :=
    RelationAffineCoverSpecialization.arithmetic_relation_affine_cover_specialization B rfl U.prescribedTotalSpace
      (U.prescribedOverlap π) hX hZ src t W hW hcover hInv N₀ hN₀
  have ht : t ≫ a = DescentCocycleChange.DescentCocycle.base π a := U.prescribedOverlapTarget_base hU π hk
  let er := DescentCocycleChange.DescentCocycle.equivalenceRelation π a t ht
    (U.prescribedOverlapTarget_normalized hU π hk hrigid)
    (U.prescribedOverlapTarget_cocycle hU π hk hrigid)
  exact ⟨D, hdiv, φ, hbase,
    ChangedDescentAffineCover.baseChanged_effective_descent_of_invariant_cover (Spec.map (CommRingCat.ofHom φ)) π a
      (DescentCocycleChange.DescentCocycle.base π a) src t (IsPullback.of_hasPullback (a ≫ π) π).flip ht er
      W' hW' hcover' hInv'⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.PrescribedSchemeDescentDenominator.ArithmeticPELComparison
