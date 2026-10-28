import OAI.NumberTheory.PadicHodge.IntegralComparison.DualFrameCoefficientPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoefficientLinePurity

/-! # Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.Purity

noncomputable section

/-! Canonical quotient-coefficient purity for finite projective modules.
Finite dual frames prove bijectivity and vanishing but do not enter the
resulting evaluation map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.CoefficientEvaluation

variable (R Q : Type u) [CommRing R] [CommRing Q] [Algebra R Q]
  (hQ : Function.Surjective (algebraMap R Q))
  (T : ModuleCat.{u} R) (n : ℕ)
  (P : ProjectiveResolution (ModuleCat.of R Q))
  (e : Quotient.CoefficientEvaluation.group R T n P ≅ ModuleCat.of R Q)
  (M : Type u) [AddCommGroup M] [Module Q M] [Module R M] [IsScalarTower R Q M]
  [Module.Finite Q M] [Module.Projective Q M]
  (PM : ProjectiveResolution (ModuleCat.of R M))

def scalarEquiv : Quotient.CoefficientEvaluation.group R T n PM ≃ₗ[R] (M →ₗ[Q] Q) :=
  LinearEquiv.ofBijective (Quotient.CoefficientEvaluation.dualMap R Q hQ T n P e M PM) (by
    obtain ⟨ι, hι, hb⟩ := IntegralComparison.Finite.DualFrame.exists_frame Q M
    let := hι
    exact (DualFrameCoefficientPurity.equiv R Q hQ T n P e M PM hb.some).bijective)

variable (L : Type u) [AddCommGroup L] [Module Q L] [Module R L] [IsScalarTower R Q L]
  (eL : Quotient.CoefficientEvaluation.group R T n P ≅ ModuleCat.of R L)

def equiv : Quotient.CoefficientEvaluation.group R T n PM ≃ₗ[R] (M →ₗ[Q] L) :=
  (scalarEquiv R Q hQ T n P e M PM).trans
    ((LinearEquiv.congrRight (CoefficientLinePurity.quotientEquiv R Q hQ L
      (e.toLinearEquiv.symm.trans eL.toLinearEquiv))).restrictScalars R)

theorem equiv_apply (x : Quotient.CoefficientEvaluation.group R T n PM) (m : M) :
    equiv R Q hQ T n P e M PM L eL x m =
      eL.hom (Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) P PM (Quotient.CoefficientEvaluation.point R Q M m) n x) := by
  change eL.hom (e.inv (e.hom (Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) P PM (Quotient.CoefficientEvaluation.point R Q M m) n x))) = _
  rw [Iso.hom_inv_id_apply]

theorem independent_scalar_frame (e' : Quotient.CoefficientEvaluation.group R T n P ≅ ModuleCat.of R Q) :
    equiv R Q hQ T n P e M PM L eL = equiv R Q hQ T n P e' M PM L eL := by
  ext x m
  simp only [equiv_apply]

theorem coefficient_map (u : Q →ₗ[Q] M) (x : Quotient.CoefficientEvaluation.group R T n PM) :
    eL.hom (Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) P PM (ModuleCat.ofHom (u.restrictScalars R)) n x) =
      equiv R Q hQ T n P e M PM L eL x (u 1) := by
  rw [equiv_apply]
  have hu : ModuleCat.ofHom (u.restrictScalars R) = Quotient.CoefficientEvaluation.point R Q M (u 1) := by
    ext q
    change u q = q • u 1
    simpa only [smul_eq_mul, mul_one] using u.map_smul q 1
  rw [hu]

variable (M' : Type u) [AddCommGroup M'] [Module Q M'] [Module R M'] [IsScalarTower R Q M']
  [Module.Finite Q M'] [Module.Projective Q M']
  (PM' : ProjectiveResolution (ModuleCat.of R M')) (f : M →ₗ[Q] M')

theorem naturality (x : Quotient.CoefficientEvaluation.group R T n PM') (m : M) :
    equiv R Q hQ T n P e M PM L eL
      (Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) PM PM' (ModuleCat.ofHom (f.restrictScalars R)) n x) m =
    equiv R Q hQ T n P e M' PM' L eL x (f m) := by
  rw [equiv_apply, equiv_apply]
  have hf : Quotient.CoefficientEvaluation.point R Q M m ≫ ModuleCat.ofHom (f.restrictScalars R) = Quotient.CoefficientEvaluation.point R Q M' (f m) := by
    ext q
    exact f.map_smul q m
  rw [← hf, Resolution.CohomologyMaps.map_comp]
  rfl

theorem isZero (h : IsZero (Quotient.CoefficientEvaluation.group R T n P)) : IsZero (Quotient.CoefficientEvaluation.group R T n PM) := by
  obtain ⟨ι, hι, hb⟩ := IntegralComparison.Finite.DualFrame.exists_frame Q M
  let := hι
  let b := hb.some
  apply (IsZero.iff_id_eq_zero _).mpr
  have hs := congrArg (fun f => Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) PM PM f n)
    (DualFrameCoefficientPurity.sum_projection_point R Q M b)
  rw [Resolution.CohomologyMaps.map_sum, Resolution.CohomologyMaps.map_id] at hs
  simp_rw [Resolution.CohomologyMaps.map_comp _ PM P PM] at hs
  have hz (i : ι) : Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) PM P
      (DualFrameCoefficientPurity.projection R Q M b i) n = 0 := h.eq_of_src _ _
  simp only [hz, comp_zero, Finset.sum_const_zero] at hs
  exact hs.symm

theorem exactAt
    (h : ((IntegralComparison.ProjectiveResolution.HomNaturality.functor (Resolution.CohomologyMaps.homFunctor R T)).obj
      (Opposite.op P.complex)).ExactAt n) :
    ((IntegralComparison.ProjectiveResolution.HomNaturality.functor (Resolution.CohomologyMaps.homFunctor R T)).obj
      (Opposite.op PM.complex)).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at h ⊢
  exact isZero R Q T n P M PM h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveCoefficient.Purity
