import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ShortComplexOf
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CompletionCokernelEq

/-! # Short Complex Comm -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ShortComplexComm.Construction.ShortComplexCompletion

noncomputable section

/-! Replacing the middle term of a short complex by chosen cokernel generators. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {R : Type u} [CommRing R]
variable (S : ShortComplex (ModuleCat.{v} R))
variable {F : Type v} [AddCommGroup F] [Module R F] (v : F →ₗ[R] S.X₂)

def first : (S.f.hom.coprod v).ker →ₗ[R] S.X₁ :=
  -((LinearMap.fst R S.X₁ F).comp (S.f.hom.coprod v).ker.subtype)

theorem first_comm :
    S.f.hom.comp (first S v) =
      v.comp (CokernelCompletion.Construction.CokernelCompletionKernel.projection S.f.hom v) := by
  ext x
  change S.f (-x.val.1) = v x.val.2
  rw [map_neg]
  exact neg_eq_iff_add_eq_zero.mpr x.property

def complex : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.moduleCatMk (CokernelCompletion.Construction.CokernelCompletionKernel.projection S.f.hom v)
    (S.g.hom.comp v) (by
      rw [LinearMap.comp_assoc, ← first_comm, ← LinearMap.comp_assoc]
      have h : S.g.hom.comp S.f.hom = 0 := ModuleCat.hom_ext_iff.mp S.zero
      rw [h, LinearMap.zero_comp])

def comparison : complex S v ⟶ S where
  τ₁ := ModuleCat.ofHom (first S v)
  τ₂ := ModuleCat.ofHom v
  τ₃ := 𝟙 _
  comm₁₂ := ModuleCat.hom_ext (first_comm S v)
  comm₂₃ := by ext x; rfl

theorem quasiIso (h : Function.Surjective (S.f.hom.coprod v)) :
    ShortComplex.QuasiIso (comparison S v) := by
  have hc : IsIso (ShortComplex.opcyclesMap (comparison S v)) := by
    apply ShortComplexOf.Construction.ShortComplexComparison.opcycles_iso
    · intro y
      obtain ⟨⟨z, x⟩, hx⟩ := h y
      exact ⟨x, z, (add_comm _ _).trans hx⟩
    · intro x hx
      have hk : x ∈ (CompletionCokernelEq.Construction.CompletionCokernel.map S.f.hom v).ker :=
        (Submodule.Quotient.mk_eq_zero S.f.hom.range).mpr hx
      rw [CompletionCokernelEq.Construction.CompletionCokernel.kernel_eq_range] at hk
      exact hk
  have : Mono (comparison S v).τ₃ := inferInstanceAs (Mono (𝟙 S.X₃))
  exact ⟨ShortComplex.isIso_homologyMap_of_isIso_opcyclesMap_of_mono hc inferInstance⟩

theorem outgoing_range (h : Function.Surjective (S.f.hom.coprod v)) :
    (S.g.hom.comp v).range = S.g.hom.range := by
  apply le_antisymm (LinearMap.range_comp_le_range _ _)
  rintro y ⟨x, rfl⟩
  obtain ⟨⟨m, a⟩, ha⟩ := h x
  refine ⟨a, ?_⟩
  change S.g (v a) = S.g x
  have hx : S.f m + v a = x := ha
  rw [← hx, map_add, S.moduleCat_zero_apply, zero_add]

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ShortComplexComm.Construction.ShortComplexCompletion
