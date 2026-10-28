import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousBracketChange
import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.LieLocalExponential
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # Change Derivative -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.ChangeDerivative.Construction

noncomputable section

/-! The derivative of an exponential change of basis is the
derivation defect. The bracket perturbation contributes the identity. -/

open NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
  [FiniteDimensional ℝ L]

local instance bracketEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance bracketEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance bracketBilinear_normed : NormedAddCommGroup (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance bracketBilinear_space : NormedSpace ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance bracketParameters_normed :
    NormedAddCommGroup ((L →L[ℝ] L) × (L →L[ℝ] L →L[ℝ] L)) := inferInstance
local instance bracketParameters_space :
    NormedSpace ℝ ((L →L[ℝ] L) × (L →L[ℝ] L →L[ℝ] L)) := inferInstance

def continuousBracketExponentialPerturbation (B : L →L[ℝ] L →L[ℝ] L)
    (p : (L →L[ℝ] L) × (L →L[ℝ] L →L[ℝ] L)) : L →L[ℝ] L →L[ℝ] L :=
  ContinuousBracketChange.Construction.continuousBracketTransform (exp p.1) (exp (-p.1)) (B + p.2) - B

omit [FiniteDimensional ℝ L] in
theorem continuousBracketExponentialPerturbation_zero (B : L →L[ℝ] L →L[ℝ] L) :
    continuousBracketExponentialPerturbation B 0 = 0 := by
  ext x y
  simp [continuousBracketExponentialPerturbation, ContinuousBracketChange.Construction.continuousBracketTransform_apply]

theorem continuousBracketExponentialPerturbation_hasStrictFDerivAt
    (B : L →L[ℝ] L →L[ℝ] L) :
    HasStrictFDerivAt (continuousBracketExponentialPerturbation B)
      ((Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B).coprod
        (ContinuousLinearMap.id ℝ (L →L[ℝ] L →L[ℝ] L))) 0 := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  let fst := ContinuousLinearMap.fst ℝ (L →L[ℝ] L) (L →L[ℝ] L →L[ℝ] L)
  let snd := ContinuousLinearMap.snd ℝ (L →L[ℝ] L) (L →L[ℝ] L →L[ℝ] L)
  let flipMap := (ContinuousLinearMap.flipₗᵢ ℝ L L L).toContinuousLinearEquiv.toContinuousLinearMap
  have hp := Minkowski.LieLocalExponential.Construction.hasStrictFDerivAt_exp_linear_zero fst
  have hn := Minkowski.LieLocalExponential.Construction.hasStrictFDerivAt_exp_linear_zero (-fst)
  have hb := (hasStrictFDerivAt_const B (0 : (L →L[ℝ] L) × (L →L[ℝ] L →L[ℝ] L))).add
    snd.hasStrictFDerivAt
  have hfirst := hb.clm_comp hn
  have hflip := flipMap.hasStrictFDerivAt.comp 0 hfirst
  have hsecond := hflip.clm_comp hn
  have hpre := flipMap.hasStrictFDerivAt.comp 0 hsecond
  have hpost := (ContinuousLinearMap.compL ℝ L L L).hasStrictFDerivAt.comp 0 hp
  have hd := (hpost.clm_comp hpre).sub_const B
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro p
  apply ContinuousLinearMap.ext
  intro x
  apply ContinuousLinearMap.ext
  intro y
  simp [Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect_apply, fst, snd, flipMap]
  abel

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.ChangeDerivative.Construction
