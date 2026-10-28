import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceFiniteAffineOpens
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceSpecializationNaturality
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.InvariantCoverLocalization

/-! # Source Invariant Affine Cover -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceInvariantAffineCover.Coefficients

noncomputable section

/-! A finite invariant affine cover spreads on the original arithmetic
scheme's coefficient base change, and becomes a cover with all invariance
equations after one nonzero coefficient is inverted. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R K : Type} [CommRing R] [IsNoetherianRing R] [Field K] [Algebra R K]

theorem fixed_source_invariant_affine_cover_away {I G : Type} [Finite I] [Finite G]
    (X : Over (Spec (.of R))) (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    (a : G → (X ⟶ X))
    (U : I → ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X).left.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (hInv : ∀ g i, ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
      (a g)).left ⁻¹ᵁ U i = U i) :
    ∃ (s : Finset K) (r : ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s), r ≠ 0 ∧
      ∃ V : I → ((Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).obj X).left.Opens,
        (∀ i, IsAffineOpen (V i)) ∧
        (∀ x : ((Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).obj X).left,
          r ∉ (((Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).obj X).hom x).asIdeal → ∃ i, x ∈ V i) ∧
        (∀ g i (x : ((Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).obj X).left),
          r ∉ (((Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).obj X).hom x).asIdeal →
          (((Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).map (a g)).left x ∈ V i ↔ x ∈ V i)) := by
  obtain ⟨s, V, hV, hpre⟩ := SourceFiniteAffineOpens.Coefficients.fixed_source_finite_affine_opens X hX U hU
  let M := CoefficientModels.Coefficients.fixedSourceModel R K s X hX
  have : IsLocallyNoetherian (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R K M.coefficients) :=
    Coefficient.Finiteness.Coefficients.coefficientBase_locallyNoetherian R K M.coefficients
  have hfp := Coefficient.Finiteness.Coefficients.baseChange_finitePresentation (CoefficientModels.Coefficients.parameterBaseMap R K s) X hX
  have : LocallyOfFinitePresentation M.model.hom := hfp.1
  have : QuasiCompact M.model.hom := hfp.2.1
  have : IsLocallyNoetherian M.model.left := LocallyOfFiniteType.isLocallyNoetherian M.model.hom
  have : CompactSpace M.model.left := QuasiCompact.compactSpace_of_compactSpace M.model.hom
  have : IsNoetherian M.model.left := ⟨⟩
  let a₀ := fun g => (Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).map (a g)
  let aK := fun g => (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map (a g)
  have hc : (⨆ i, M.specialization ⁻¹ᵁ V i) = ⊤ := (iSup_congr hpre).trans hcover
  have hi : ∀ g i, (aK g).left ⁻¹ᵁ (M.specialization ⁻¹ᵁ V i) = M.specialization ⁻¹ᵁ V i := by
    intro g i
    exact (congrArg (fun W => (aK g).left ⁻¹ᵁ W) (hpre i)).trans ((hInv g i).trans (hpre i).symm)
  obtain ⟨r, hr, hcov, hinv⟩ := Coefficient.InvariantCoverLocalization.Coefficients.finite_invariant_cover_away M V a₀ aK
    (fun g => SourceSpecializationNaturality.Coefficients.fixedSourceModel_specialization_naturality s X hX (a g)) hc hi
  exact ⟨s, r, hr, V, hV, hcov, hinv⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceInvariantAffineCover.Coefficients
