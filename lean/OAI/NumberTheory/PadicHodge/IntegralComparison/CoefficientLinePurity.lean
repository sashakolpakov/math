import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FreeCoefficientPurity

/-! # Coefficient Line Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CoefficientLinePurity

noncomputable section

/-! The finite-coefficient purity isomorphism with its intrinsic target line.
The scalar trivialization cancels from its evaluation formula. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.CoefficientEvaluation

variable (R Q : Type u) [CommRing R] [CommRing Q] [Algebra R Q]
  (hQ : Function.Surjective (algebraMap R Q))
  (L : Type u) [AddCommGroup L] [Module Q L] [Module R L] [IsScalarTower R Q L]

def quotientEquiv (e : Q ≃ₗ[R] L) : Q ≃ₗ[Q] L :=
  { e.toAddEquiv with
    map_smul' := fun q x => by
      obtain ⟨r, rfl⟩ := hQ q
      change e ((algebraMap R Q) r • x) = (algebraMap R Q) r • e x
      rw [IsScalarTower.algebraMap_smul Q r x, IsScalarTower.algebraMap_smul Q r (e x)]
      exact e.map_smul r x }

variable (T : ModuleCat.{u} R) (n : ℕ)
  (P : ProjectiveResolution (ModuleCat.of R Q))
  (e : Quotient.CoefficientEvaluation.group R T n P ≅ ModuleCat.of R Q)
  (eL : Quotient.CoefficientEvaluation.group R T n P ≅ ModuleCat.of R L)
  (M : Type u) [AddCommGroup M] [Module Q M] [Module R M] [IsScalarTower R Q M]
  (PM : ProjectiveResolution (ModuleCat.of R M))
  {ι : Type u} [Fintype ι] (b : Module.Basis ι Q M)

def equiv : Quotient.CoefficientEvaluation.group R T n PM ≃ₗ[R] (M →ₗ[Q] L) :=
  (Finite.FreeCoefficientPurity.equiv R Q hQ T n P e M PM b).trans
    ((LinearEquiv.congrRight (quotientEquiv R Q hQ L
      (e.toLinearEquiv.symm.trans eL.toLinearEquiv))).restrictScalars R)

theorem equiv_apply (x : Quotient.CoefficientEvaluation.group R T n PM) (m : M) :
    equiv R Q hQ L T n P e eL M PM b x m =
      eL.hom (Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) P PM (Quotient.CoefficientEvaluation.point R Q M m) n x) := by
  change eL.hom (e.inv (e.hom (Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) P PM (Quotient.CoefficientEvaluation.point R Q M m) n x))) = _
  rw [Iso.hom_inv_id_apply]

theorem independent_scalar_frame (e' : Quotient.CoefficientEvaluation.group R T n P ≅ ModuleCat.of R Q) :
    equiv R Q hQ L T n P e eL M PM b = equiv R Q hQ L T n P e' eL M PM b := by
  ext x m
  simp only [equiv_apply]

theorem independent_basis {κ : Type u} [Fintype κ] (b' : Module.Basis κ Q M) :
    equiv R Q hQ L T n P e eL M PM b = equiv R Q hQ L T n P e eL M PM b' := by
  ext x m
  simp only [equiv_apply]

variable (M' : Type u) [AddCommGroup M'] [Module Q M'] [Module R M'] [IsScalarTower R Q M']
  (PM' : ProjectiveResolution (ModuleCat.of R M'))
  {κ : Type u} [Fintype κ] (b' : Module.Basis κ Q M')
  (f : M →ₗ[Q] M')

theorem naturality (x : Quotient.CoefficientEvaluation.group R T n PM') (m : M) :
    equiv R Q hQ L T n P e eL M PM b
      (Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) PM PM' (ModuleCat.ofHom (f.restrictScalars R)) n x) m =
    equiv R Q hQ L T n P e eL M' PM' b' x (f m) := by
  rw [equiv_apply, equiv_apply]
  have hf : Quotient.CoefficientEvaluation.point R Q M m ≫ ModuleCat.ofHom (f.restrictScalars R) = Quotient.CoefficientEvaluation.point R Q M' (f m) := by
    ext q
    exact f.map_smul q m
  rw [← hf, Resolution.CohomologyMaps.map_comp]
  rfl

theorem coefficient_map (u : Q →ₗ[Q] M) (x : Quotient.CoefficientEvaluation.group R T n PM) :
    eL.hom (Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) P PM (ModuleCat.ofHom (u.restrictScalars R)) n x) =
      equiv R Q hQ L T n P e eL M PM b x (u 1) := by
  rw [equiv_apply]
  have hu : ModuleCat.ofHom (u.restrictScalars R) = Quotient.CoefficientEvaluation.point R Q M (u 1) := by
    ext q
    change u q = q • u 1
    exact (by simpa only [smul_eq_mul, mul_one] using u.map_smul q 1)
  rw [hu]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CoefficientLinePurity
