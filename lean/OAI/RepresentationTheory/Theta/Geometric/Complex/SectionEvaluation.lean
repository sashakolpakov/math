import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

/-! # Section Evaluation -/

namespace OAI.RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation

noncomputable section

/-! Evaluation of actual regular sections at actual complex scheme points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

variable {X Y : Scheme}

def complexSectionValue (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) (U : X.Opens)
    (hp : p (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ U) : Γ(X, U) →+* ℂ :=
  (Scheme.ΓSpecIso (.of ℂ)).hom.hom.comp (p.appLE U ⊤ (by
    intro x _
    change p x ∈ U
    rwa [Subsingleton.elim x (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)])).hom

theorem complexSectionValue_congr (p q : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) (h : p = q) (U : X.Opens)
    (hp : p (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ U) (hq : q (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ U) (s : Γ(X, U)) :
    complexSectionValue p U hp s = complexSectionValue q U hq s := by
  subst q
  rfl

theorem complexSectionValue_restrict (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) (U V : X.Opens)
    (hVU : V ≤ U) (hp : p (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ V) (s : Γ(X, U)) :
    complexSectionValue p V hp (X.presheaf.map (homOfLE hVU).op s) =
      complexSectionValue p U (hVU hp) s := by
  have h := p.map_appLE (show (⊤ : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase.Opens) ≤ p ⁻¹ᵁ V from by
    intro x _
    change p x ∈ V
    rwa [Subsingleton.elim x (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)]) (homOfLE hVU).op
  exact congrArg (fun f : Γ(X, U) ⟶ Γ(AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) =>
    (Scheme.ΓSpecIso (.of ℂ)).hom (f s)) h

theorem complexSectionValue_pullback (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) (f : X ⟶ Y)
    (U : Y.Opens) (V : X.Opens) (hV : V ≤ f ⁻¹ᵁ U)
    (hp : p (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ V) (s : Γ(Y, U)) :
    complexSectionValue p V hp (f.appLE U V hV s) =
      complexSectionValue (p ≫ f) U (hV hp) s := by
  have h := Scheme.Hom.appLE_comp_appLE p f U V ⊤ hV (by
    intro x _
    change p x ∈ V
    rwa [Subsingleton.elim x (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)])
  exact congrArg (fun g : Γ(Y, U) ⟶ Γ(AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) =>
    (Scheme.ΓSpecIso (.of ℂ)).hom (g s)) h

theorem complexSectionValue_spec {R : Type} [CommRing R] (a : R →+* ℂ) (r : R) :
    complexSectionValue (Spec.map (CommRingCat.ofHom a)) ⊤ (by trivial)
      ((Scheme.ΓSpecIso (.of R)).inv r) = a r := by
  change (Scheme.ΓSpecIso (.of ℂ)).hom
    ((Spec.map (CommRingCat.ofHom a)).appTop ((Scheme.ΓSpecIso (.of R)).inv r)) = a r
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom a)
  have h' := ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso (.of R)).inv r)
  change (Scheme.ΓSpecIso (.of ℂ)).hom
    ((Spec.map (CommRingCat.ofHom a)).appTop ((Scheme.ΓSpecIso (.of R)).inv r)) =
    a ((Scheme.ΓSpecIso (.of R)).hom ((Scheme.ΓSpecIso (.of R)).inv r)) at h'
  rw [Iso.inv_hom_id_apply] at h'
  exact h'

theorem complexSectionValue_open (U : X.Opens) (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ U.toScheme) (s : Γ(X, U)) :
    complexSectionValue (p ≫ U.ι) U (p (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)).property s =
      complexSectionValue p ⊤ (by trivial) (U.topIso.inv s) := by
  have h := complexSectionValue_pullback p U.ι U ⊤ U.ι_preimage_self.ge (by trivial) s
  have hm : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    exact congrArg X.presheaf.map (Subsingleton.elim _ _)
  rw [hm] at h
  exact h.symm

theorem complexSectionValue_affineIso {R : Type} [CommRing R]
    (e : X ≅ Spec (.of R)) (a : R →+* ℂ) (r : R) :
    complexSectionValue (Spec.map (CommRingCat.ofHom a) ≫ e.inv) ⊤ (by trivial)
      (e.hom.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) = a r := by
  have h := complexSectionValue_pullback (Spec.map (CommRingCat.ofHom a) ≫ e.inv) e.hom
    ⊤ ⊤ (by simp) (by trivial) ((Scheme.ΓSpecIso (.of R)).inv r)
  have ht : e.hom.appLE ⊤ ⊤ (by simp) = e.hom.appTop := e.hom.appLE_eq_app
  rw [ht] at h
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  exact h.trans (complexSectionValue_spec a r)

theorem complexRingHom_units_zpow {R : Type} [CommRing R] (f : R →+* ℂ) (u : Rˣ) (d : ℤ) :
    f ((u ^ d : Rˣ) : R) = (f (u : R)) ^ d := by
  change ((Units.map f.toMonoidHom (u ^ d) : ℂˣ) : ℂ) = _
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

end

end OAI.RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation
