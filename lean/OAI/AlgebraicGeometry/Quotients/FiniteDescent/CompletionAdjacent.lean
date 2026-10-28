import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ShortComplexComm

/-! # Completion Adjacent -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CompletionAdjacent.Construction.CompletionAdjacentCohomology

noncomputable section

/-! A cokernel completion also preserves cohomology at its neighboring terms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {R : Type u} [CommRing R]
variable (S : ShortComplex (ModuleCat.{v} R))
variable {F : Type v} [AddCommGroup F] [Module R F] (v : F →ₗ[R] S.X₃)

def incoming : S.X₁ →ₗ[R] (S.g.hom.coprod v).ker :=
  ((-S.f.hom).prod 0).codRestrict _ (by
    intro x
    change S.g (-S.f x) + v 0 = 0
    rw [map_neg, S.moduleCat_zero_apply, neg_zero, map_zero, add_zero])

def leftComplex : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.moduleCatMk (incoming S v)
    (CokernelCompletion.Construction.CokernelCompletionKernel.projection S.g.hom v) (by ext x; rfl)

def leftComparison : leftComplex S v ⟶ S where
  τ₁ := 𝟙 _
  τ₂ := ModuleCat.ofHom
    (-((LinearMap.fst R S.X₂ F).comp (S.g.hom.coprod v).ker.subtype))
  τ₃ := ModuleCat.ofHom v
  comm₁₂ := by ext x; exact (neg_neg (S.f x)).symm
  comm₂₃ := by
    ext x
    change S.g (-x.val.1) = v x.val.2
    rw [map_neg]
    exact neg_eq_iff_add_eq_zero.mpr x.property

theorem left_quasiIso : ShortComplex.QuasiIso (leftComparison S v) := by
  have hc : IsIso (ShortComplex.cyclesMap (leftComparison S v)) := by
    apply ShortComplexOf.Construction.ShortComplexComparison.cycles_iso
    · intro y hy
      let x : (S.g.hom.coprod v).ker := ⟨(-y, 0), by
        change S.g (-y) + v 0 = 0
        rw [map_neg, hy, neg_zero, map_zero, add_zero]⟩
      exact ⟨x, rfl, neg_neg y⟩
    · intro x hx hf
      apply Subtype.ext
      apply Prod.ext
      · change x.val.1 = 0
        exact neg_eq_zero.mp hf
      · exact hx
  have : Epi (leftComparison S v).τ₁ := inferInstanceAs (Epi (𝟙 S.X₁))
  exact ⟨ShortComplex.isIso_homologyMap_of_isIso_cyclesMap_of_epi hc inferInstance⟩

variable (T : ShortComplex (ModuleCat.{v} R))
variable {P : Type v} [AddCommGroup P] [Module R P] (w : P →ₗ[R] T.X₁)

def rightComplex : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.moduleCatMk (T.f.hom.comp w) T.g.hom (by
    rw [← LinearMap.comp_assoc]
    have hz : T.g.hom.comp T.f.hom = 0 := ModuleCat.hom_ext_iff.mp T.zero
    rw [hz, LinearMap.zero_comp])

def rightComparison : rightComplex T w ⟶ T where
  τ₁ := ModuleCat.ofHom w
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  comm₁₂ := by ext x; rfl
  comm₂₃ := by ext x; rfl

theorem right_quasiIso (hw : (T.f.hom.comp w).range = T.f.hom.range) :
    ShortComplex.QuasiIso (rightComparison T w) := by
  have hc : IsIso (ShortComplex.opcyclesMap (rightComparison T w)) := by
    apply ShortComplexOf.Construction.ShortComplexComparison.opcycles_iso
    · intro y
      exact ⟨y, 0, by change y + T.f 0 = y; rw [map_zero, add_zero]⟩
    · intro x hx
      change x ∈ (T.f.hom.comp w).range
      rw [hw]
      exact hx
  have : Mono (rightComparison T w).τ₃ := inferInstanceAs (Mono (𝟙 T.X₃))
  exact ⟨ShortComplex.isIso_homologyMap_of_isIso_opcyclesMap_of_mono hc inferInstance⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CompletionAdjacent.Construction.CompletionAdjacentCohomology
