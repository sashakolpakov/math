import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Specialization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentUniformization

/-! # Reduced Complex PEL -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ReducedComplexPEL

noncomputable section

/-! The actual complex base change of the reduced reference model,
with its surjective closed inclusion into ReferenceFamily's original complex fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (κ : K →+* ℂ)

abbrev reducedComplexPEL : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj (Reduction.reduction M.space)

def reducedComplexPELInclusion : reducedComplexPEL M κ ⟶ M.complexFiber κ :=
  (Over.pullback (Spec.map (CommRingCat.ofHom κ))).map (Reduction.reductionι M.space)

instance reducedComplexPELInclusion_closed : IsClosedImmersion (reducedComplexPELInclusion M κ).left :=
  MorphismProperty.of_isPullback (Specialization.base_change_square (Spec.map (CommRingCat.ofHom κ))
    (Reduction.reductionι M.space)) inferInstance

instance reducedComplexPELInclusion_surjective : Surjective (reducedComplexPELInclusion M κ).left := by
  have : Surjective (Reduction.reductionι M.space).left := ⟨fun x => by
    have h : x ∈ Set.range (Reduction.reductionι M.space).left := by rw [Reduction.reduction_range]; trivial
    exact h⟩
  exact MorphismProperty.of_isPullback (Specialization.base_change_square (Spec.map (CommRingCat.ofHom κ))
    (Reduction.reductionι M.space)) inferInstance

instance reducedComplexPELInclusion_mono : Mono (reducedComplexPELInclusion M κ) :=
  Over.mono_of_mono_left _

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ReducedComplexPEL
