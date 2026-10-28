/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleQuasicoherent.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Module.TransferInstance

/-! # Restriction Section Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionSectionFiniteness

noncomputable section

/-! Finiteness passes from sections on an open to native global sections of its restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem module_restrict_sections_finite_of_sections_finite {X : Scheme.{u}}
    (M : X.Modules) (U : X.Opens) [Module.Finite Γ(X, U) Γ(M, U)] :
    Module.Finite Γ(U.toScheme, ⊤) Γ(M.restrict U.ι, ⊤) := by
  let eR' := U.ι.appIso (⊤ : U.toScheme.Opens)
  let eR : Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) ≃+* Γ(U.toScheme, ⊤) :=
    eR'.commRingCatIsoToRingEquiv
  let eM' := M.restrictAppIso U.ι ⊤
  let σ : Γ(U.toScheme, ⊤) →+*
      Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) := eR'.inv.hom
  let eM : Γ(M.restrict U.ι, ⊤) →ₛₗ[σ]
      Γ(M, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) :=
    { toFun := eM'.hom
      map_add' := eM'.hom.hom.map_add
      map_smul' := by
        intro r x
        change eM'.hom (r • x) = eR'.inv.hom r • eM'.hom x
        exact Scheme.Modules.smul_restrictAppIso_hom_apply U.ι M ⊤ r x }
  have hσ : Function.Surjective σ := by
    change Function.Surjective
      (eR.symm : Γ(U.toScheme, ⊤) →+*
        Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens)))
    exact eR.symm.surjective
  let : RingHomSurjective σ := ⟨hσ⟩
  have heM : Function.Bijective eM := by
    change Function.Bijective eM'.hom
    exact ConcreteCategory.bijective_of_isIso eM'.hom
  have htarget : Module.Finite
      Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens))
      Γ(M, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) := by
    rw [U.ι_image_top]
    infer_instance
  exact (eM.finite_iff_of_bijective heM).mpr htarget

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionSectionFiniteness
