import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.GlobalSectionMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.CoefficientEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SpecGlobalSectionIdentities

/-! # Coefficient Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.CoefficientRecovery

noncomputable section

/-! The coefficient ring map of a normalized projective chart is
recovered from its structural morphism. Passing through the spectrum's
global-section isomorphism recovers the native appTop coefficient map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] {T : Scheme.{u}} {n : ℕ}

theorem schemeCoefficientMap_toSpec_map (c : R →+* Γ(T, ⊤)) :
    Coefficient.ModulePresheaf.schemeCoefficientMap (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom c)) = c := by
  rw [Field.CoefficientEuler.schemeCoefficientMap_specMap_comp, SpecGlobalSectionIdentities.schemeCoefficientMap_toSpecΓ, RingHom.id_comp]

theorem projectiveChartMap_structural_coefficients
    (c : R →+* Γ(T, ⊤)) (v : Fin (n + 1) → Γ(T, ⊤)) (i : Fin (n + 1)) (hi : v i = 1) :
    Coefficient.ModulePresheaf.schemeCoefficientMap (Evaluation.projectiveChartMap c v i hi ≫ (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom) = c := by
  rw [Evaluation.projectiveChartMap_over]
  exact schemeCoefficientMap_toSpec_map c

theorem schemeCoefficientMap_comp_specGlobalIso (p : T ⟶ Spec (.of R)) :
    (Coefficient.ModulePresheaf.schemeCoefficientMap p).comp (Scheme.ΓSpecIso (.of R)).hom.hom = p.appTop.hom := by
  ext r
  change p.appTop ((Scheme.ΓSpecIso (.of R)).inv ((Scheme.ΓSpecIso (.of R)).hom r)) = p.appTop r
  exact congrArg p.appTop (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of R)).hom_inv_id r)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.CoefficientRecovery
