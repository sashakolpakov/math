import OAI.AlgebraicGeometry.Betti.ProjectiveComponentForms

/-! # Projective Component Pure Equiv -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveComponentPureEquiv.SmoothProjectivePresentation

noncomputable section

/-!
# Pure form families and their actual component forms

The pure families on a smooth projective presentation are identified with
families of pure forms on its actual integral components. For closed pure
forms the identification reuses the existing equivalence of closed families
with componentwise closed forms. All component evaluations are literal.
-/

variable (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

/-- Pure families are precisely families of genuine pure component forms. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPureFormsEquiv (p q : ℕ) :
    P.componentPureForms p q ≃ₗ[ℂ]
      (∀ C : irreducibleComponents P.carrier,
        Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm (P.componentVariety C).analyticModel
          (P.componentVariety C).analyticSpace p q) where
  toFun form C :=
    ⟨form.val C, (P.mem_componentPureForms_iff p q form.val).mp form.property C⟩
  invFun form :=
    ⟨fun C => (form C).val,
      (P.mem_componentPureForms_iff p q _).mpr fun C => (form C).property⟩
  left_inv form := by
    apply Subtype.ext
    rfl
  right_inv form := by
    funext C
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPureFormsEquiv_apply (p q : ℕ) (form : P.componentPureForms p q)
    (C : irreducibleComponents P.carrier) :
    (P.componentPureFormsEquiv p q form C).val = form.val C :=
  rfl

@[simp]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPureFormsEquiv_symm_apply (p q : ℕ)
    (form : ∀ C : irreducibleComponents P.carrier,
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm (P.componentVariety C).analyticModel
        (P.componentVariety C).analyticSpace p q)
    (C : irreducibleComponents P.carrier) :
    ((P.componentPureFormsEquiv p q).symm form).val C = (form C).val :=
  rfl

/-- Closed pure families are precisely families of genuine closed pure
component forms, using the existing closed-family identification. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPureClosedFormsEquiv (p q : ℕ) :
    P.componentPureClosedForms p q ≃ₗ[ℂ]
      (∀ C : irreducibleComponents P.carrier,
        ManifoldPureClasses.pureClosedManifoldForms (P.componentVariety C).analyticModel
          (P.componentVariety C).analyticSpace p q) where
  toFun form C :=
    ⟨P.componentClosedFormsEquiv (p + q) form.val C,
      (P.mem_componentPureForms_iff p q form.val.val).mp form.property C⟩
  invFun form :=
    ⟨(P.componentClosedFormsEquiv (p + q)).symm (fun C => (form C).val),
      (P.mem_componentPureForms_iff p q _).mpr fun C => (form C).property⟩
  left_inv form := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv form := by
    funext C
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPureClosedFormsEquiv_apply (p q : ℕ)
    (form : P.componentPureClosedForms p q) (C : irreducibleComponents P.carrier) :
    (P.componentPureClosedFormsEquiv p q form C).val.val = form.val.val C :=
  rfl

@[simp]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPureClosedFormsEquiv_symm_apply (p q : ℕ)
    (form : ∀ C : irreducibleComponents P.carrier,
      ManifoldPureClasses.pureClosedManifoldForms (P.componentVariety C).analyticModel
        (P.componentVariety C).analyticSpace p q)
    (C : irreducibleComponents P.carrier) :
    ((P.componentPureClosedFormsEquiv p q).symm form).val.val C = (form C).val.val :=
  rfl

end

end OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveComponentPureEquiv.SmoothProjectivePresentation
