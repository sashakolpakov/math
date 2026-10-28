import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.RelationInvariantAffineCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.CoefficientSpecialization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RelationCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RelationAffineCoverIso

/-! # Relation Affine Cover Specialization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.RelationAffineCoverSpecialization

noncomputable section

/-! A finite relation-invariant affine complex cover specializes to
an actual invariant affine cover over a localized ring of integers,
on the literal base changes of both original relation schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.RelationInvariantAffineCover.Coefficients

theorem arithmetic_relation_affine_cover_specialization
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ) [Algebra B.R ℂ]
    (hAlg : algebraMap B.R ℂ = B.embedding.comp B.toField)
    {I : Type} [Finite I]
    (X Z : Over B.base) (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    (hZ : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Z.hom) (a b : Z ⟶ X)
    (U : I → ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R ℂ)))).obj X).left.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (hInv : ∀ i, ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R ℂ)))).map a).left ⁻¹ᵁ U i =
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R ℂ)))).map b).left ⁻¹ᵁ U i)
    (N₀ : ℕ) (hN₀ : N₀ ≠ 0) :
    ∃ D : Base.ArithmeticBaseExtension B.extension.carrier B.embedding,
      N₀ ∣ D.denominator ∧ ∃ φ : B.R →+* D.R,
        D.toField.comp φ = (algebraMap B.extension.carrier D.extension.carrier).comp B.toField ∧
        ∃ V : I → ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).left.Opens,
          (∀ i, IsAffineOpen (V i)) ∧ iSup V = ⊤ ∧
          (∀ i, ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).map a).left ⁻¹ᵁ V i =
            ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).map b).left ⁻¹ᵁ V i) := by
  obtain ⟨s, r, hr, V, hV, hcov, hinv⟩ := Fixed.RelationInvariantAffineCover.Coefficients.fixed_relation_invariant_affine_cover_away X Z hX hZ a b U hU hcover hInv
  obtain ⟨D, hdiv, ψ, hunit, hbase⟩ := B.coefficient_parameter_integral_specialization hAlg s r hr N₀ hN₀
  let φ := ψ.comp (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R ℂ s))
  let f := Fixed.CoefficientModels.Coefficients.parameterBaseMap B.R ℂ s
  let k := Spec.map (CommRingCat.ofHom ψ)
  let c := Spec.map (CommRingCat.ofHom φ)
  have hkc : k ≫ f = c := by
    change Spec.map (CommRingCat.ofHom ψ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R ℂ s))) = _
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R ℂ s)))
      (CommRingCat.ofHom ψ)).symm
  let e := Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso f k c hkc
  let aS := (Over.pullback f).map a
  let bS := (Over.pullback f).map b
  obtain ⟨haff, hfull, hstable⟩ := RelationCover.relation_affine_cover_baseChange_of_unit
    ((Over.pullback f).obj X) ((Over.pullback f).obj Z) aS bS V r hV hcov hinv ψ hunit
  refine ⟨D, hdiv, φ, hbase, ?_⟩
  exact RelationAffineCoverIso.relation_invariant_affine_cover_of_iso (e.app X).symm (e.app Z).inv
    ((Over.pullback c).map a) ((Over.pullback c).map b)
    ((Over.pullback k).map aS) ((Over.pullback k).map bS)
    (e.inv.naturality a) (e.inv.naturality b)
    (fun i => pullback.fst ((Over.pullback f).obj X).hom k ⁻¹ᵁ V i) haff hfull hstable

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.RelationAffineCoverSpecialization
