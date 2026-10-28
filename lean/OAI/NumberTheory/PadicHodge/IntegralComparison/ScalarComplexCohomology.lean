import OAI.NumberTheory.PadicHodge.IntegralComparison.SurjectiveScalarComplexSequence
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.HomologySequence

/-! # Scalar Complex Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarComplexCohomology

noncomputable section

/-! Multiplication through a scalar-image quotient remains multiplication on actual cohomology. -/

open _root_.CategoryTheory

universe u v

variable {R : Type u} [CommRing R] {K L : CochainComplex (ModuleCat.{v} R) ℕ}

theorem homology_smul (r : R) (f : K ⟶ L) (i : ℕ) :
    HomologicalComplex.homologyMap (r • f) i = r • HomologicalComplex.homologyMap f i := by
  exact ShortComplex.homologyMap_smul ((HomologicalComplex.shortComplexFunctor _ _ i).map f) r

theorem homology_scalar (r : R) (i : ℕ) :
    HomologicalComplex.homologyMap (r • 𝟙 K) i = r • 𝟙 (K.homology i) := by
  rw [homology_smul, HomologicalComplex.homologyMap_id]

variable (q : K ⟶ L) (hq : ∀ a, Function.Surjective (q.f a)) (r : R)
  (hk : ∀ a (x : K.X a), q.f a x = 0 ↔ r • x = 0)

theorem quotient_inclusion : q ≫ SurjectiveScalarComplexSequence.inclusion q hq r hk = r • 𝟙 K := by
  apply HomologicalComplex.Hom.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact SurjectiveScalarComplexSequence.inclusion_apply q hq r hk a x

theorem inclusion_quotient : SurjectiveScalarComplexSequence.inclusion q hq r hk ≫ q = r • 𝟙 L := by
  apply HomologicalComplex.Hom.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hq a y
  change q.f a ((SurjectiveScalarComplexSequence.inclusion q hq r hk).f a (q.f a x)) = r • q.f a x
  rw [SurjectiveScalarComplexSequence.inclusion_apply]
  exact (q.f a).hom.map_smul r x

theorem cohomology_quotient_inclusion (i : ℕ) (x : K.homology i) :
    HomologicalComplex.homologyMap (SurjectiveScalarComplexSequence.inclusion q hq r hk) i
      (HomologicalComplex.homologyMap q i x) = r • x := by
  have h := (congrArg (fun f => HomologicalComplex.homologyMap f i) (quotient_inclusion q hq r hk)).trans
    (homology_scalar r i)
  rw [HomologicalComplex.homologyMap_comp] at h
  exact congrArg (fun a => a x) h

theorem cohomology_inclusion_quotient (i : ℕ) (x : L.homology i) :
    HomologicalComplex.homologyMap q i
      (HomologicalComplex.homologyMap (SurjectiveScalarComplexSequence.inclusion q hq r hk) i x) = r • x := by
  have h := (congrArg (fun f => HomologicalComplex.homologyMap f i) (inclusion_quotient q hq r hk)).trans
    (homology_scalar r i)
  rw [HomologicalComplex.homologyMap_comp] at h
  exact congrArg (fun a => a x) h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarComplexCohomology
