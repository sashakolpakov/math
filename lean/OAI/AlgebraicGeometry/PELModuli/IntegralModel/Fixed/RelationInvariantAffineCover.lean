import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceFiniteAffineOpens
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.SourceMorphismSpecialization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.InvariantCoverLocalization

/-! # Relation Invariant Affine Cover -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.RelationInvariantAffineCover

noncomputable section

/-! A finite invariant affine cover for an actual relation spreads on
the literal original schemes after one common coefficient localization.
The two relation arrows may have a different source from the parameter. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Coefficients
variable {R K : Type} [CommRing R] [IsNoetherianRing R] [Field K] [Algebra R K]

theorem fixed_relation_invariant_affine_cover_away {I : Type} [Finite I]
    (X Z : Over (Spec (.of R))) (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    (hZ : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Z.hom) (a b : Z ⟶ X)
    (U : I → ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X).left.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (hInv : ∀ i, ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map a).left ⁻¹ᵁ U i =
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map b).left ⁻¹ᵁ U i) :
    ∃ (s : Finset K) (r : ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s), r ≠ 0 ∧
      ∃ V : I → ((Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).obj X).left.Opens,
        (∀ i, IsAffineOpen (V i)) ∧
        (∀ x : ((Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).obj X).left,
          r ∉ (((Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).obj X).hom x).asIdeal → ∃ i, x ∈ V i) ∧
        (∀ i (z : ((Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).obj Z).left),
          r ∉ (((Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).obj Z).hom z).asIdeal →
          (((Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).map a).left z ∈ V i ↔
            ((Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)).map b).left z ∈ V i)) := by
  classical
  have : Fintype I := Fintype.ofFinite I
  obtain ⟨s, V, hV, hpre⟩ := SourceFiniteAffineOpens.Coefficients.fixed_source_finite_affine_opens X hX U hU
  let MX := CoefficientModels.Coefficients.fixedSourceModel R K s X hX
  let MZ := CoefficientModels.Coefficients.fixedSourceModel R K s Z hZ
  have : IsNoetherian MX.model.left := SourceMorphismSpecialization.Coefficients.fixedSourceModel_noetherian s X hX
  have : IsNoetherian MZ.model.left := SourceMorphismSpecialization.Coefficients.fixedSourceModel_noetherian s Z hZ
  let F := Over.pullback (CoefficientModels.Coefficients.parameterBaseMap R K s)
  let G := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  have hc : MX.specialization ⁻¹ᵁ iSup V = MX.specialization ⁻¹ᵁ ⊤ := by
    ext x
    change MX.specialization x ∈ iSup V ↔ MX.specialization x ∈ (⊤ : MX.model.left.Opens)
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have hx : x ∈ iSup U := hcover ▸ Set.mem_univ x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    have hi' : x ∈ MX.specialization ⁻¹ᵁ V i :=
      (congrArg (fun W => x ∈ W) (hpre i)).mpr hi
    exact Opens.mem_iSup.mpr ⟨i, hi'⟩
  obtain ⟨r₀, hr₀, hcov⟩ := Coefficient.InvariantCoverLocalization.Coefficients.coefficient_open_equality_away MX (iSup V) ⊤ hc
  change ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s at r₀
  have heq (i : I) : MZ.specialization ⁻¹ᵁ ((F.map a).left ⁻¹ᵁ V i) =
      MZ.specialization ⁻¹ᵁ ((F.map b).left ⁻¹ᵁ V i) := by
    have hn (c : Z ⟶ X) : MZ.specialization ⁻¹ᵁ ((F.map c).left ⁻¹ᵁ V i) =
        (G.map c).left ⁻¹ᵁ U i := by
      have hmap : MZ.specialization ≫ (F.map c).left = (G.map c).left ≫ MX.specialization :=
        SourceMorphismSpecialization.Coefficients.fixedSourceModel_specialization_map s Z X hZ hX c
      exact (Scheme.Hom.comp_preimage MZ.specialization (F.map c).left (V i)).symm.trans
        ((congrArg (fun q => q ⁻¹ᵁ V i) hmap).trans
          ((Scheme.Hom.comp_preimage (G.map c).left MX.specialization (V i)).trans
            (congrArg (fun W => (G.map c).left ⁻¹ᵁ W) (hpre i))))
    exact (hn a).trans ((hInv i).trans (hn b).symm)
  choose r hr hgood using fun i : I =>
    Coefficient.InvariantCoverLocalization.Coefficients.coefficient_open_equality_away MZ ((F.map a).left ⁻¹ᵁ V i)
      ((F.map b).left ⁻¹ᵁ V i) (heq i)
  change I → ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s at r
  let d := ∏ i, r i
  refine ⟨s, r₀ * d, mul_ne_zero hr₀ (Finset.prod_ne_zero_iff.mpr (fun i _ => hr i)),
    V, hV, ?_, ?_⟩
  · intro x hx
    exact Opens.mem_iSup.mp ((hcov x
      (fun h => hx ((MX.model.hom x).asIdeal.mul_mem_right d h))).mpr trivial)
  · intro i z hz
    apply hgood i z
    intro h
    have hd : r i ∣ r₀ * d := (Finset.dvd_prod_of_mem r (Finset.mem_univ i)).trans (dvd_mul_left d r₀)
    exact hz ((MZ.model.hom z).asIdeal.mem_of_dvd hd h)

end Coefficients

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Fixed.RelationInvariantAffineCover
