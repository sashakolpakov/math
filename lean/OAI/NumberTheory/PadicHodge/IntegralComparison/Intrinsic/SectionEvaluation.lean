import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SmoothClosedSections

/-! # Section Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionEvaluation

noncomputable section

/-! Evaluation on the original affine section algebra, together with
its kernel and its behavior under restriction to an open neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (s : Spec (CommRingCat.of R) ⟶ X.left) (hs : s ≫ X.hom = 𝟙 _)
  (U : X.left.Opens) (hU : ⊤ ≤ s ⁻¹ᵁ U)

include hs in
theorem retraction :
    X.hom.appLE ⊤ U (by simp) ≫ s.appLE U ⊤ hU = 𝟙 _ := by
  rw [Scheme.Hom.appLE_comp_appLE]
  have h : ∀ (f : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R))
      (hf : f = 𝟙 _) (e : ⊤ ≤ f ⁻¹ᵁ ⊤), f.appLE ⊤ ⊤ e = 𝟙 _ := by
    intro f hf e
    subst f
    change 𝟙 _ ≫ (Spec (CommRingCat.of R)).presheaf.map (𝟙 (op ⊤)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact h _ hs _

def evaluation : SmoothClosedSections.ring R X U →ₐ[R] R where
  toRingHom := (s.appLE U ⊤ hU ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom
  commutes' r := by
    have h := congrArg (fun a => (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ a ≫
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom) (retraction R X s hs U hU)
    simp only [Category.assoc, Category.id_comp, Iso.inv_hom_id] at h
    exact ConcreteCategory.congr_hom h r

include hU in
theorem kernel [IsClosedImmersion s] (hUa : IsAffineOpen U) :
    RingHom.ker (evaluation R X s hs U hU).toRingHom = s.ker.ideal ⟨U, hUa⟩ := by
  have he : s ⁻¹ᵁ U = ⊤ := top_unique hU
  have hm : IsIso ((Spec (CommRingCat.of R)).presheaf.map (homOfLE hU).op) := by
    have : IsIso (homOfLE hU) := by
      change IsIso (eqToHom he.symm)
      infer_instance
    infer_instance
  have hres := (ConcreteCategory.bijective_of_isIso
    ((Spec (CommRingCat.of R)).presheaf.map (homOfLE hU).op)).injective
  have hiso := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom).injective
  change RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.comp
    (s.appLE U ⊤ hU).hom) = _
  rw [RingHom.ker_comp_of_injective _ hiso, Scheme.Hom.ker_apply]
  exact RingHom.ker_comp_of_injective _ hres

theorem principal_contains (a : SmoothClosedSections.ring R X U)
    (ha : evaluation R X s hs U hU a = 1) :
    ⊤ ≤ s ⁻¹ᵁ X.left.basicOpen a := by
  have he : s.appLE U ⊤ hU a = 1 := by
    apply (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom).injective
    exact ha.trans (map_one _).symm
  have h := Scheme.basicOpen_appLE s ⊤ U hU a
  rw [he, Scheme.basicOpen_one, top_inf_eq] at h
  exact h.le

variable (V : X.left.Opens) (hVU : V ≤ U) (hV : ⊤ ≤ s ⁻¹ᵁ V)

theorem restriction (a : SmoothClosedSections.ring R X U) :
    evaluation R X s hs V hV
      (((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map (homOfLE hVU).op).hom a) =
        evaluation R X s hs U hU a := by
  have h := s.map_appLE hV (homOfLE hVU).op
  exact congrArg (fun b => (Scheme.ΓSpecIso (CommRingCat.of R)).hom b)
    (ConcreteCategory.congr_hom h a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionEvaluation
