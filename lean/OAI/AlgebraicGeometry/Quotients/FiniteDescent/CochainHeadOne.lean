import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainHeadD
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CompletionAdjacent

/-! # Cochain Head One -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainHeadOne

noncomputable section

/-! The first pair of terms of a cochain complex can be replaced by a
cokernel completion, without changing its cohomology. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

namespace Construction.CochainHeadCompletion

variable {R : Type u} [CommRing R]
variable (C : CochainComplex (ModuleCat.{v} R) ℕ)
variable {F : Type v} [AddCommGroup F] [Module R F] (v : F →ₗ[R] C.X 1)

def term : ℕ → ModuleCat.{v} R
  | 0 => ModuleCat.of R (((C.d 0 1).hom.coprod v).ker)
  | 1 => ModuleCat.of R F
  | n + 2 => C.X (n + 2)

def differential : ∀ n, term C v n ⟶ term C v (n + 1)
  | 0 => ModuleCat.ofHom (CokernelCompletion.Construction.CokernelCompletionKernel.projection (C.d 0 1).hom v)
  | 1 => ModuleCat.ofHom v ≫ C.d 1 2
  | n + 2 => C.d (n + 2) (n + 3)

theorem square_zero (n : ℕ) : differential C v n ≫ differential C v (n + 1) = 0 := by
  rcases n with _ | _ | n
  · exact (ShortComplexComm.Construction.ShortComplexCompletion.complex (C.sc' 0 1 2) v).zero
  · change (ModuleCat.ofHom v ≫ C.d 1 2) ≫ C.d 2 3 = 0
    rw [Category.assoc, C.d_comp_d, comp_zero]
  · exact C.d_comp_d _ _ _

def complex : CochainComplex (ModuleCat.{v} R) ℕ :=
  CochainComplex.of (term C v) (differential C v) (square_zero C v)

theorem d_zero : (complex C v).d 0 1 =
    ModuleCat.ofHom (CokernelCompletion.Construction.CokernelCompletionKernel.projection (C.d 0 1).hom v) :=
  CochainComplex.of_d (term C v) (differential C v) 0

theorem d_one : (complex C v).d 1 2 = ModuleCat.ofHom v ≫ C.d 1 2 :=
  CochainComplex.of_d (term C v) (differential C v) 1

theorem d_succ_succ (n : ℕ) : (complex C v).d (n + 2) (n + 3) = C.d (n + 2) (n + 3) :=
  CochainComplex.of_d (term C v) (differential C v) (n + 2)

def comparisonComponent : ∀ n, (complex C v).X n ⟶ C.X n
  | 0 => ModuleCat.ofHom (ShortComplexComm.Construction.ShortComplexCompletion.first (C.sc' 0 1 2) v)
  | 1 => ModuleCat.ofHom v
  | _ + 2 => 𝟙 _

def comparison : complex C v ⟶ C :=
  CochainComplex.ofHom (comparisonComponent C v) (by
    intro n
    rcases n with _ | _ | n
    · change ModuleCat.ofHom (ShortComplexComm.Construction.ShortComplexCompletion.first (C.sc' 0 1 2) v) ≫ C.d 0 1 =
        (complex C v).d 0 1 ≫ ModuleCat.ofHom v
      rw [d_zero]
      exact ModuleCat.hom_ext (ShortComplexComm.Construction.ShortComplexCompletion.first_comm (C.sc' 0 1 2) v)
    · change ModuleCat.ofHom v ≫ C.d 1 2 = (complex C v).d 1 2 ≫ 𝟙 _
      rw [d_one, Category.comp_id]
    · change 𝟙 _ ≫ C.d (n + 2) (n + 3) = (complex C v).d (n + 2) (n + 3) ≫ 𝟙 _
      rw [d_succ_succ, Category.id_comp, Category.comp_id])

theorem quasiIso_zero : QuasiIsoAt (comparison C v) 0 := by
  rw [CochainComplex.quasiIsoAt₀_iff]
  let φ := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} R)
    (ComplexShape.up ℕ) 0 0 1).map (comparison C v)
  have hc : IsIso (ShortComplex.cyclesMap φ) := by
    apply ShortComplexOf.Construction.ShortComplexComparison.cycles_iso
    · intro y hy
      change ↥(C.X 0) at y
      change (C.d 0 1) y = 0 at hy
      let x : ((C.d 0 1).hom.coprod v).ker := ⟨(-y, 0), by
        change (C.d 0 1) (-y) + v 0 = 0
        rw [map_neg, hy, neg_zero, map_zero, add_zero]⟩
      refine ⟨x, ?_, neg_neg y⟩
      change (complex C v).d 0 1 x = 0
      rw [d_zero]
      rfl
    · intro x hx hf
      change (complex C v).d 0 1 x = 0 at hx
      rw [d_zero] at hx
      apply Subtype.ext
      exact Prod.ext (neg_eq_zero.mp hf) hx
  apply ShortComplexOf.Construction.ShortComplexComparison.quasiIso_of_cycles_iso φ
  · exact (complex C v).shape 0 0 (by decide)
  · exact C.shape 0 0 (by decide)

theorem quasiIso_one (h : Function.Surjective ((C.d 0 1).hom.coprod v)) :
    QuasiIsoAt (comparison C v) 1 := by
  rw [quasiIsoAt_iff' _ 0 1 2 (by simp) (by simp)]
  let φ := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} R)
    (ComplexShape.up ℕ) 0 1 2).map (comparison C v)
  have hc : IsIso (ShortComplex.opcyclesMap φ) := by
    apply ShortComplexOf.Construction.ShortComplexComparison.opcycles_iso
    · intro y
      obtain ⟨⟨z, x⟩, hx⟩ := h y
      exact ⟨x, z, (add_comm _ _).trans hx⟩
    · intro x hx
      have hk : x ∈ (CompletionCokernelEq.Construction.CompletionCokernel.map (C.d 0 1).hom v).ker :=
        (Submodule.Quotient.mk_eq_zero (C.d 0 1).hom.range).mpr hx
      rw [CompletionCokernelEq.Construction.CompletionCokernel.kernel_eq_range] at hk
      change x ∈ ((complex C v).d 0 1).hom.range
      rw [d_zero]
      exact hk
  have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 (C.X 2)))
  exact ⟨ShortComplex.isIso_homologyMap_of_isIso_opcyclesMap_of_mono hc inferInstance⟩

theorem quasiIso_two (h : Function.Surjective ((C.d 0 1).hom.coprod v)) :
    QuasiIsoAt (comparison C v) 2 := by
  rw [quasiIsoAt_iff' _ 1 2 3 (by simp) (by simp)]
  let φ := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} R)
    (ComplexShape.up ℕ) 1 2 3).map (comparison C v)
  have hc : IsIso (ShortComplex.opcyclesMap φ) := by
    apply ShortComplexOf.Construction.ShortComplexComparison.opcycles_iso
    · intro y
      change ↥(C.X 2) at y
      exact ⟨y, 0, by change y + (C.d 1 2) 0 = y; rw [map_zero, add_zero]⟩
    · intro x hx
      change x ∈ ((complex C v).d 1 2).hom.range
      rw [d_one]
      change x ∈ ((C.d 1 2).hom.comp v).range
      exact (ShortComplexComm.Construction.ShortComplexCompletion.outgoing_range (C.sc' 0 1 2) v h).ge hx
  have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 (C.X 3)))
  exact ⟨ShortComplex.isIso_homologyMap_of_isIso_opcyclesMap_of_mono hc inferInstance⟩

theorem quasiIso_higher (n : ℕ) : QuasiIsoAt (comparison C v) (n + 3) := by
  rw [quasiIsoAt_iff' _ (n + 2) (n + 3) (n + 4) (by simp) (by simp)]
  let φ := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} R)
    (ComplexShape.up ℕ) (n + 2) (n + 3) (n + 4)).map (comparison C v)
  have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 (C.X (n + 2))))
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (C.X (n + 3))))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 (C.X (n + 4))))
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ

theorem quasiIso (h : Function.Surjective ((C.d 0 1).hom.coprod v)) :
    QuasiIso (comparison C v) := by
  constructor
  intro n
  rcases n with _ | _ | _ | n
  · exact quasiIso_zero C v
  · exact quasiIso_one C v h
  · exact quasiIso_two C v h
  · exact quasiIso_higher C v n

end Construction.CochainHeadCompletion

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainHeadOne
