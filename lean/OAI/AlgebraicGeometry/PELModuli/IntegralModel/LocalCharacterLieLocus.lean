import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRankConormalCriterion
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRankCharacter
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ModuleRankLocus
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ReductionLocusClassification
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Local Character Lie Locus -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocalCharacterLieLocus

noncomputable section

/-! The literal geometric Lie-rank condition has a constructed reduced
locally closed locus on every actual integral-action chart. All reduced
test schemes are classified, without a finiteness assumption on the tests. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {E : Type} [Field E] [NumberField E] {S : Scheme.{0}} [IsLocallyNoetherian S]
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (χ : NumberField.RingOfIntegers E →+* Γ(S, ⊤)) (r : ℕ)
  (C : Section.ActionCharts.SectionMorphismChart A.scheme.hom η[A.scheme].left
    (fun i => (ρ.map (IntegralModel.Finite.Actions.integralActionBasis E i)).left))

theorem exists_reduced_local_character_lie_locus :
    ∃ (Z : Over S) (j : Z ⟶ Over.mk C.V.ι),
      IsReduced Z.left ∧ IsImmersion j.left ∧ QuasiCompact j.left ∧
      ∀ (T : Over S) [IsReduced T.left] (x : T ⟶ Over.mk C.V.ι),
        (∀ (k : Type) [Field k] [IsAlgClosed k] (p : Spec (.of k) ⟶ T.left),
          LieRankCharacter.CharacterLieRank A ρ χ r ((p ≫ x.left) ≫ C.V.ι)) ↔
            ∃! f : T ⟶ Z, f ≫ j = x := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
  let : Module.Finite Γ(C.V.toScheme, ⊤) (RingHom.ker C.targetSection.appTop.hom).Cotangent :=
    (C.conormal_finite_projective (AbelianConormalCharts.abelian_unit_section A)).1
  let : IsNoetherianRing Γ(C.V.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top C.V.toScheme⟩
  let d := C.conormalOperator (AbelianConormalCharts.abelian_unit_section A)
    (AbelianConormalCharts.action_over A ρ (IntegralModel.Finite.Actions.integralActionBasis E)) (AbelianConormalCharts.action_unit_section A ρ (IntegralModel.Finite.Actions.integralActionBasis E))
  let t := fun i => C.V.ι.appTop (χ (IntegralModel.Finite.Actions.integralActionBasis E i))
  let L := ConormalEigenquotient.conormalEigenquotient d t
  let : Module.FinitePresentation Γ(C.V.toScheme, ⊤) L :=
    ConormalEigenquotient.conormalEigenquotient_finitePresentation d t
  obtain ⟨Z, j, hj, hqc, hZ⟩ := @Reduced.ModuleRankLocus.exists_reduced_test_module_rank_locus S
    (Over.mk C.V.ι) L _ _ (ConormalEigenquotient.conormalEigenquotient_finitePresentation d t) r
  let := hj
  let := hqc
  have hjred : IsImmersion ((Reduction.reductionι Z).left ≫ j.left) := inferInstance
  have hqred : QuasiCompact ((Reduction.reductionι Z).left ≫ j.left) := inferInstance
  refine ⟨Reduction.reduction Z, Reduction.reductionι Z ≫ j, inferInstance, hjred, hqred, ?_⟩
  intro T hT x
  rw [ReductionLocusClassification.existsUnique_lift_reduction_iff, ← hZ T x]
  have h (k : Type) [Field k] (q : Spec (.of k) ⟶ C.V.toScheme) :
      letI := Affine.SectionLie.AffineSectionLie.baseFieldAlgebra q
      LieRankCharacter.CharacterLieRank A ρ χ r (q ≫ C.V.ι) ↔
        Module.finrank k (k ⊗[Γ(C.V.toScheme, ⊤)] L) = r := by
    apply LieRankConormalCriterion.AlgebraicLie.hasLieRank_iff_chart_quotient A ρ C q
      ((HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap (q ≫ C.V.ι)).comp χ) t
    intro i
    exact RingHom.congr_fun (TangentPointCoefficients.RelativeTangent.coefficientMap_postcomp q C.V.ι)
      (χ (IntegralModel.Finite.Actions.integralActionBasis E i))
  constructor
  · intro hx k hk ha p
    exact (h k (p ≫ x.left)).mp (hx k p)
  · intro hx k hk ha p
    exact (h k (p ≫ x.left)).mpr (hx k p)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocalCharacterLieLocus
