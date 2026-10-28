import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceInvariantAffineCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.CoefficientSpecialization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoverUnitBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.InvariantAffineCoverIso

/-! # Invariant Affine Cover Specialization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.InvariantAffineCoverSpecialization

noncomputable section

/-! A finite invariant affine cover of the complex fiber specializes
to an actual invariant affine cover over a localized ring of integers,
on the literal base change of the original arithmetic scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceInvariantAffineCover.Coefficients

theorem arithmetic_invariant_affine_cover_specialization
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ) [Algebra B.R ℂ]
    (hAlg : algebraMap B.R ℂ = B.embedding.comp B.toField)
    {I G : Type} [Finite I] [Finite G]
    (X : Over B.base) (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (a : G → (X ⟶ X))
    (U : I → ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R ℂ)))).obj X).left.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (hInv : ∀ g i, ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R ℂ)))).map
      (a g)).left ⁻¹ᵁ U i = U i) (N₀ : ℕ) (hN₀ : N₀ ≠ 0) :
    ∃ D : Base.ArithmeticBaseExtension B.extension.carrier B.embedding,
      N₀ ∣ D.denominator ∧ ∃ φ : B.R →+* D.R,
        D.toField.comp φ = (algebraMap B.extension.carrier D.extension.carrier).comp B.toField ∧
        ∃ V : I → ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).left.Opens,
          (∀ i, IsAffineOpen (V i)) ∧ iSup V = ⊤ ∧
          (∀ g i, ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).map (a g)).left ⁻¹ᵁ V i = V i) := by
  obtain ⟨s, r, hr, V, hV, hcov, hinv⟩ := Fixed.SourceInvariantAffineCover.Coefficients.fixed_source_invariant_affine_cover_away X hX a U hU hcover hInv
  obtain ⟨D, hdiv, ψ, hunit, hbase⟩ := B.coefficient_parameter_integral_specialization hAlg s r hr N₀ hN₀
  let φ := ψ.comp (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R ℂ s))
  let f := Fixed.CoefficientModels.Coefficients.parameterBaseMap B.R ℂ s
  let b := Spec.map (CommRingCat.ofHom ψ)
  let c := Spec.map (CommRingCat.ofHom φ)
  have hbc : b ≫ f = c := by
    change Spec.map (CommRingCat.ofHom ψ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R ℂ s))) = _
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R ℂ s)))
      (CommRingCat.ofHom ψ)).symm
  let e := Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso f b c hbc
  let aS := fun g => (Over.pullback f).map (a g)
  obtain ⟨haff, hfull, hstable⟩ := CoverUnitBaseChange.invariant_affine_cover_baseChange_of_unit
    ((Over.pullback f).obj X) V aS r hV hcov hinv ψ hunit
  refine ⟨D, hdiv, φ, hbase, ?_⟩
  exact InvariantAffineCoverIso.invariant_affine_cover_of_iso (e.app X).symm
    (fun g => (Over.pullback c).map (a g)) (fun g => (Over.pullback b).map (aS g))
    (fun g => e.inv.naturality (a g))
    (fun i => pullback.fst ((Over.pullback f).obj X).hom b ⁻¹ᵁ V i) haff hfull hstable

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.InvariantAffineCoverSpecialization
