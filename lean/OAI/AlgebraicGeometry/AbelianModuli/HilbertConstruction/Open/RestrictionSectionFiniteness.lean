import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Module.TransferInstance

/-! # Restriction Section Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionSectionFiniteness

noncomputable section

/-! Finiteness passes through the semilinear section isomorphism for any open immersion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem module_openRestrict_sections_finite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) (U : X.Opens)
    [Module.Finite Γ(Y, f ''ᵁ U) Γ(M, f ''ᵁ U)] :
    Module.Finite Γ(X, U) Γ(M.restrict f, U) := by
  let eR' := f.appIso U
  let eR : Γ(Y, f ''ᵁ U) ≃+* Γ(X, U) := eR'.commRingCatIsoToRingEquiv
  let eM' := M.restrictAppIso f U
  let σ : Γ(X, U) →+* Γ(Y, f ''ᵁ U) := eR'.inv.hom
  let eM : Γ(M.restrict f, U) →ₛₗ[σ] Γ(M, f ''ᵁ U) :=
    { toFun := eM'.hom
      map_add' := eM'.hom.hom.map_add
      map_smul' := by
        intro r x
        change eM'.hom (r • x) = eR'.inv.hom r • eM'.hom x
        exact Scheme.Modules.smul_restrictAppIso_hom_apply f M U r x }
  have hσ : Function.Surjective σ := eR.symm.surjective
  let : RingHomSurjective σ := ⟨hσ⟩
  have heM : Function.Bijective eM := ConcreteCategory.bijective_of_isIso eM'.hom
  exact (eM.finite_iff_of_bijective heM).mpr inferInstance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionSectionFiniteness
