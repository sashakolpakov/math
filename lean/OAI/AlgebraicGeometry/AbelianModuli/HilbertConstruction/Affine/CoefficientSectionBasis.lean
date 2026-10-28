import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionFrameCriterion

/-! # Coefficient Section Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoefficientSectionBasis

noncomputable section

/-! A section basis over the global ring of Spec R is a basis over R
with precisely the same actual sheaf sections. No field assumption is
needed for this coefficient transport. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (p : X ⟶ Spec (.of R)) (M : X.Modules) {ι : Type v}

def affineCoefficientSectionBasis
    (b : Module.Basis ι Γ(Spec (.of R), ⊤) ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor p.appTop.hom).obj M)) :
    Module.Basis ι R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M) := by
  let e := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  letI : Module R ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor p.appTop.hom).obj M) :=
    inferInstanceAs (Module R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M))
  exact b.mapCoeffs e (by
    intro c x
    change (M.smul (X.presheaf.map (𝟙 (.op (⊤ : X.Opens)))
      (Coefficient.ModulePresheaf.schemeCoefficientMap p (e c)))).hom x =
        (M.smul (X.presheaf.map (𝟙 (.op (⊤ : X.Opens))) (p.appTop c))).hom x
    have hc : Coefficient.ModulePresheaf.schemeCoefficientMap p (e c) = p.appTop c :=
      congrArg p.appTop (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of R)).hom_inv_id c)
    rw [hc])

theorem affineCoefficientSectionBasis_family
    (b : Module.Basis ι Γ(Spec (.of R), ⊤) ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor p.appTop.hom).obj M)) :
    Coefficient.RingSectionBasis.coefficientRingBasisFamily (Coefficient.ModulePresheaf.schemeCoefficientMap p) M (affineCoefficientSectionBasis p M b) =
      Coefficient.RingSectionBasis.coefficientRingBasisFamily p.appTop.hom M b := by
  funext i
  unfold Coefficient.RingSectionBasis.coefficientRingBasisFamily affineCoefficientSectionBasis
  erw [Module.Basis.mapCoeffs_apply]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoefficientSectionBasis
