import OAI.AlgebraicGeometry.Quotients.FiniteDescent.HomologyInjective
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.RingTheory.Finiteness.Prod

/-! # Pair Cohomology -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PairCohomology

noncomputable section

/-! Two cohomology comparisons combine into a single detector. The criterion
is stated after arbitrary scalar extension, so it applies at local fibers. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Construction.PairCohomologyDetector

variable {R : Type u} [CommRing R]
variable {S T₁ T₂ Q₁ Q₂ : ShortComplex (ModuleCat.{u} R)}
variable (r₁ : S ⟶ T₁) (r₂ : S ⟶ T₂) (p₁ : T₁ ⟶ Q₁) (p₂ : T₂ ⟶ Q₂)

abbrev target := ModuleCat.of R (Q₁.X₂ × Q₂.X₂)

def map : S.X₂ ⟶ target (Q₁ := Q₁) (Q₂ := Q₂) :=
  ModuleCat.ofHom ((r₁.τ₂ ≫ p₁.τ₂).hom.prod (r₂.τ₂ ≫ p₂.τ₂).hom)

theorem incoming_zero (h₁ : Q₁.f = 0) (h₂ : Q₂.f = 0) :
    S.f ≫ PairCohomologyDetector.map r₁ r₂ p₁ p₂ = 0 := by
  have e₁ : S.f ≫ (r₁.τ₂ ≫ p₁.τ₂) = 0 := by
    rw [← Category.assoc, ← r₁.comm₁₂, Category.assoc, ← p₁.comm₁₂, h₁, comp_zero, comp_zero]
  have e₂ : S.f ≫ (r₂.τ₂ ≫ p₂.τ₂) = 0 := by
    rw [← Category.assoc, ← r₂.comm₁₂, Category.assoc, ← p₂.comm₁₂, h₂, comp_zero, comp_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Prod.ext (ConcreteCategory.congr_hom e₁ x) (ConcreteCategory.congr_hom e₂ x)

theorem finite [Module.Finite R Q₁.X₂] [Module.Finite R Q₂.X₂] :
    Module.Finite R (target (Q₁ := Q₁) (Q₂ := Q₂)) := inferInstance

theorem free [Module.Free R Q₁.X₂] [Module.Free R Q₂.X₂] :
    Module.Free R (target (Q₁ := Q₁) (Q₂ := Q₂)) := inferInstance

theorem components_zero {A : Type u} [CommRing A] [Algebra R A]
    (z : A ⊗[R] S.X₂) (hz : (PairCohomologyDetector.map r₁ r₂ p₁ p₂).hom.baseChange A z = 0) :
    (r₁.τ₂ ≫ p₁.τ₂).hom.baseChange A z = 0 ∧
      (r₂.τ₂ ≫ p₂.τ₂).hom.baseChange A z = 0 := by
  constructor
  · have e : (LinearMap.fst R Q₁.X₂ Q₂.X₂).comp (PairCohomologyDetector.map r₁ r₂ p₁ p₂).hom =
        (r₁.τ₂ ≫ p₁.τ₂).hom := rfl
    rw [← e, LinearMap.baseChange_comp, LinearMap.comp_apply, hz, map_zero]
  · have e : (LinearMap.snd R Q₁.X₂ Q₂.X₂).comp (PairCohomologyDetector.map r₁ r₂ p₁ p₂).hom =
        (r₂.τ₂ ≫ p₂.τ₂).hom := rfl
    rw [← e, LinearMap.baseChange_comp, LinearMap.comp_apply, hz, map_zero]

theorem detects {A : Type u} [CommRing A] (a : R →+* A)
    [ShortComplex.QuasiIso ((ModuleCat.extendScalars a).mapShortComplex.map p₁)]
    [ShortComplex.QuasiIso ((ModuleCat.extendScalars a).mapShortComplex.map p₂)]
    (hjoint : ∀ z : (S.map (ModuleCat.extendScalars a)).X₂,
      (S.map (ModuleCat.extendScalars a)).g z = 0 →
      ((ModuleCat.extendScalars a).mapShortComplex.map r₁).τ₂ z ∈
        (T₁.map (ModuleCat.extendScalars a)).f.hom.range →
      ((ModuleCat.extendScalars a).mapShortComplex.map r₂).τ₂ z ∈
        (T₂.map (ModuleCat.extendScalars a)).f.hom.range →
      z ∈ (S.map (ModuleCat.extendScalars a)).f.hom.range)
    (z : (S.map (ModuleCat.extendScalars a)).X₂)
    (hz : (S.map (ModuleCat.extendScalars a)).g z = 0)
    (hb : (ModuleCat.extendScalars a).map (PairCohomologyDetector.map r₁ r₂ p₁ p₂) z = 0) :
    z ∈ (S.map (ModuleCat.extendScalars a)).f.hom.range := by
  let : Algebra R A := a.toAlgebra
  let F := (ModuleCat.extendScalars a).mapShortComplex
  obtain ⟨hb₁, hb₂⟩ := components_zero r₁ r₂ p₁ p₂ (A := A) z hb
  apply hjoint z hz
  · apply HomologyInjective.Construction.HomologyInjectiveCriterion.boundary (F.map p₁)
      ((ModuleCat.mono_iff_injective _).mp inferInstance) ((F.map r₁).τ₂ z)
    · exact (ConcreteCategory.congr_hom (F.map r₁).comm₂₃ z).trans
        (by change (F.map r₁).τ₃ ((S.map (ModuleCat.extendScalars a)).g z) = 0
            rw [hz, map_zero])
    · refine ⟨0, (map_zero _).trans (Eq.symm ?_)⟩
      change p₁.τ₂.hom.baseChange A (r₁.τ₂.hom.baseChange A z) = 0
      simpa only [ModuleCat.hom_comp, LinearMap.baseChange_comp, LinearMap.comp_apply] using hb₁
  · apply HomologyInjective.Construction.HomologyInjectiveCriterion.boundary (F.map p₂)
      ((ModuleCat.mono_iff_injective _).mp inferInstance) ((F.map r₂).τ₂ z)
    · exact (ConcreteCategory.congr_hom (F.map r₂).comm₂₃ z).trans
        (by change (F.map r₂).τ₃ ((S.map (ModuleCat.extendScalars a)).g z) = 0
            rw [hz, map_zero])
    · refine ⟨0, (map_zero _).trans (Eq.symm ?_)⟩
      change p₂.τ₂.hom.baseChange A (r₂.τ₂.hom.baseChange A z) = 0
      simpa only [ModuleCat.hom_comp, LinearMap.baseChange_comp, LinearMap.comp_apply] using hb₂

end Construction.PairCohomologyDetector

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PairCohomology
