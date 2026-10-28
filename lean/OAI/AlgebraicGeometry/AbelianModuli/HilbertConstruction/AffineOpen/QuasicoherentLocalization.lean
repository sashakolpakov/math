/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleQuasicoherent.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.SectionExtension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.SectionVanishing

/-! # Quasicoherent Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.QuasicoherentLocalization

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules Opposite _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}}

theorem affineOpen_quasicoherent_sections_localize
    (M : X.Modules) [M.IsQuasicoherent]
    (U : X.affineOpens) (f : Γ(X, U.1)) :
    let : Module Γ(X, U.1) Γ(M, X.basicOpen f) :=
      Module.compHom _ (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f))
    IsLocalizedModule.Away f
      ({
          toFun := M.presheaf.map (homOfLE (X.basicOpen_le f)).op
          map_add' :=
            (M.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.map_add
          map_smul' := fun r x ↦
            M.map_smul (homOfLE (X.basicOpen_le f)) r x
        } : Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(M, X.basicOpen f)) := by
  let : Module Γ(X, U.1) Γ(M, X.basicOpen f) :=
    Module.compHom _ (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f))
  let : IsLocalization.Away f Γ(X, X.basicOpen f) :=
    U.2.isLocalization_basicOpen f
  let ψ : Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(M, X.basicOpen f) :=
    {
      toFun := M.presheaf.map (homOfLE (X.basicOpen_le f)).op
      map_add' :=
        (M.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.map_add
      map_smul' := fun r x ↦
        M.map_smul (homOfLE (X.basicOpen_le f)) r x
    }
  change IsLocalizedModule.Away f ψ
  refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_
  · have hunit : IsUnit
        (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) f) :=
      IsLocalization.Away.algebraMap_isUnit _
    have hunitEnd := hunit.map
      (algebraMap Γ(X, X.basicOpen f)
        (Module.End Γ(X, X.basicOpen f) Γ(M, X.basicOpen f)))
    rw [Module.End.isUnit_iff] at hunitEnd ⊢
    convert hunitEnd using 1
  · intro s
    obtain ⟨n, t, ht⟩ :=
      SectionExtension.affineOpen_quasicoherent_section_clear_denominator
        M U f s
    exact ⟨n, t, ht.symm⟩
  · intro t ht
    exact
      SectionVanishing.affineOpen_quasicoherent_section_vanishing
        M U f t ht

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.QuasicoherentLocalization
