import OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.ChangeRepresentation

/-! # Continuous Bracket Representation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousBracketRepresentation.Construction

noncomputable section

/-! The infinitesimal change-of-basis representation on continuous
bilinear operations agrees with the bracket derivation defect. -/

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

local instance repEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance repEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance repBilinear_normed : NormedAddCommGroup (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance repBilinear_space : NormedSpace ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance repBilinear_finite : FiniteDimensional ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance

def continuousBilinearChangeInfinitesimal (A : L →L[ℝ] L) :
    (L →L[ℝ] L →L[ℝ] L) →L[ℝ] (L →L[ℝ] L →L[ℝ] L) :=
  ((ContinuousBracketChange.Construction.finiteBilinearEquiv.toLinearMap.comp (Bilinear.ChangeRepresentation.Construction.bilinearChangeInfinitesimal A.toLinearMap)).comp
    ContinuousBracketChange.Construction.finiteBilinearEquiv.symm.toLinearMap).toContinuousLinearMap

theorem continuousBilinearChangeInfinitesimal_apply
    (A : L →L[ℝ] L) (B : L →L[ℝ] L →L[ℝ] L) :
    continuousBilinearChangeInfinitesimal A B = Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A := by
  ext x y
  rfl

def continuousBracketRepresentation : (L →L[ℝ] L) →ₗ[ℝ]
    ((L →L[ℝ] L →L[ℝ] L) →L[ℝ] (L →L[ℝ] L →L[ℝ] L)) where
  toFun := continuousBilinearChangeInfinitesimal
  map_add' A C := by
    ext B x y
    simp only [add_apply, continuousBilinearChangeInfinitesimal_apply, map_add]
  map_smul' c A := by
    ext B x y
    simp only [smul_apply, continuousBilinearChangeInfinitesimal_apply, map_smul, RingHom.id_apply]

theorem continuousBracketRepresentation_apply
    (A : L →L[ℝ] L) (B : L →L[ℝ] L →L[ℝ] L) :
    continuousBracketRepresentation A B = Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A :=
  continuousBilinearChangeInfinitesimal_apply A B

theorem continuousBracketRepresentation_algebraic
    (A : L →L[ℝ] L) (B : L →L[ℝ] L →L[ℝ] L) :
    ContinuousBracketChange.Construction.finiteBilinearEquiv.symm (continuousBracketRepresentation A B) =
      Bilinear.ChangeRepresentation.Construction.bilinearChangeInfinitesimal A.toLinearMap (ContinuousBracketChange.Construction.finiteBilinearEquiv.symm B) := by
  ext x y
  rfl

theorem continuousBracketRepresentation_commutator (A C : L →L[ℝ] L) :
    continuousBracketRepresentation (A * C - C * A) =
      continuousBracketRepresentation A * continuousBracketRepresentation C -
        continuousBracketRepresentation C * continuousBracketRepresentation A := by
  apply ContinuousLinearMap.ext
  intro B
  apply ContinuousLinearMap.ext
  intro x
  apply ContinuousLinearMap.ext
  intro y
  simp only [sub_apply, mul_apply_eq_comp, continuousBracketRepresentation_apply,
    Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect_apply, map_sub, sub_apply]
  abel

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousBracketRepresentation.Construction
