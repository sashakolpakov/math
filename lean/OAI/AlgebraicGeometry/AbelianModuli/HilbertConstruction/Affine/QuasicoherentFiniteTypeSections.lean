/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleQuasicoherent.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverGeneratorFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.QuasicoherentLocalization
import Mathlib.RingTheory.Localization.Finiteness

/-! # Quasicoherent Finite Type Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentFiniteTypeSections

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules Opposite _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}}

theorem affineOpen_quasicoherent_finiteType_sections_finite
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(M, U.1) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  let : q.IsFiniteType := hq
  let t : Set Γ(X, U.1) :=
    { f | ∃ i, X.basicOpen f ≤ q.X i }
  have hqcover : ⨆ i, q.X i = ⊤ := by
    simpa only [IsOpenCover] using
      (Opens.coversTop_iff (T := X) q.X).mp q.coversTop
  have hopen : ⨆ f : t, X.basicOpen f.1 = U.1 := by
    apply le_antisymm
    · exact iSup_le fun f ↦ X.basicOpen_le f.1
    · calc
        U.1 = U.1 ⊓ ⊤ := by simp
        _ = U.1 ⊓ ⨆ i, q.X i := by rw [hqcover]
        _ = ⨆ i, U.1 ⊓ q.X i := by rw [inf_iSup_eq]
        _ ≤ ⨆ f : t, X.basicOpen f.1 := by
          refine iSup_le fun i ↦ ?_
          rintro x hx
          obtain ⟨f, hf, hxf⟩ :=
            U.2.exists_basicOpen_le ⟨x, hx.2⟩ hx.1
          have hle : X.basicOpen f ≤
              ⨆ f : t, X.basicOpen f.1 :=
            le_iSup_of_le ⟨f, i, hf⟩ le_rfl
          exact hle hxf
  have ht : Ideal.span t = ⊤ :=
    U.2.iSup_basicOpen_eq_self_iff.mp hopen
  let (g : t) : Algebra Γ(X, U.1) Γ(X, X.basicOpen g.1) :=
    inferInstance
  let (g : t) : Module Γ(X, U.1) Γ(M, X.basicOpen g.1) :=
    Module.compHom _ (algebraMap Γ(X, U.1) Γ(X, X.basicOpen g.1))
  let (g : t) : IsLocalization.Away g.1
      Γ(X, X.basicOpen g.1) :=
    U.2.isLocalization_basicOpen g.1
  let (g : t) : IsScalarTower Γ(X, U.1)
      Γ(X, X.basicOpen g.1) Γ(M, X.basicOpen g.1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let φ : (g : t) →
      Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(M, X.basicOpen g.1) :=
    fun g ↦
      {
        toFun := M.presheaf.map (homOfLE (X.basicOpen_le g.1)).op
        map_add' :=
          (M.presheaf.map (homOfLE (X.basicOpen_le g.1)).op).hom.map_add
        map_smul' := fun r x ↦
          M.map_smul (homOfLE (X.basicOpen_le g.1)) r x
      }
  let : ∀ g : t, IsLocalizedModule.Away g.1 (φ g) :=
    fun g ↦
      AffineOpen.QuasicoherentLocalization.affineOpen_quasicoherent_sections_localize
        M U g.1
  refine Module.Finite.of_localizationSpan'
    (Mₚ := fun g : t ↦ Γ(M, X.basicOpen g.1))
    (Rₚ := fun g : t ↦ Γ(X, X.basicOpen g.1))
    t ht φ ?_
  intro g
  obtain ⟨i, hi⟩ := g.2
  let : (q.generators i).IsFiniteType := hq.isFiniteType i
  exact OverGeneratorFiniteness.module_finite_app_of_over_generators_of_le M hi
    (U.2.basicOpen g.1) (q.generators i)

theorem affine_quasicoherent_finiteType_sections_finite [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite Γ(X, ⊤) Γ(M, ⊤) :=
  affineOpen_quasicoherent_finiteType_sections_finite M ⟨⊤, isAffineOpen_top X⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentFiniteTypeSections
