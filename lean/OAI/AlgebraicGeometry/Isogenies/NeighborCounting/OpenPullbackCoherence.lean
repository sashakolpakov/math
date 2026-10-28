import OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.Adjunction
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.NormalizedSquares

/-! # Open Pullback Coherence -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OpenPullbackCoherence

noncomputable section

/-! The canonical open pullback comparison is the adjoint comparison
of the actual composed direct images. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem conjugate_leftAdjointUniq_inv
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G) :
    conjugateEquiv a b (a.leftAdjointUniq b).inv = 𝟙 G := by
  exact (conjugateEquiv a b).apply_symm_apply (𝟙 G)

theorem conjugate_leftAdjointUniq_hom
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G) :
    conjugateEquiv b a (a.leftAdjointUniq b).hom = 𝟙 G := by
  have h := conjugateEquiv_comp a b a (a.leftAdjointUniq b).inv (a.leftAdjointUniq b).hom
  rw [conjugate_leftAdjointUniq_inv, Category.id_comp, Iso.hom_inv_id, conjugateEquiv_id] at h
  exact h

theorem conjugate_pullbackCongr_inv {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction g) (Scheme.Modules.pullbackCongr h).inv =
        (Scheme.Modules.pushforwardCongr h).hom := by
  subst g
  change conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) (𝟙 _) = _
  rw [conjugateEquiv_id]
  apply NatTrans.ext
  funext M
  apply Scheme.Modules.hom_ext
  intro U
  simp only [NatTrans.id_app, Scheme.Modules.Hom.id_app,
    Scheme.Modules.pushforwardCongr_hom_app_app, eqToHom_refl, op_id]
  exact (M.presheaf.map_id _).symm

theorem conjugate_iso_hom_of_inv
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : L₁ ≅ L₂) (v : R₁ ≅ R₂)
    (h : conjugateEquiv a b e.inv = v.hom) :
    conjugateEquiv b a e.hom = v.inv := by
  apply (cancel_epi v.hom).mp
  have hc := conjugateEquiv_comp a b a e.inv e.hom
  rw [h, Iso.hom_inv_id, conjugateEquiv_id] at hc
  exact hc.trans v.hom_inv_id.symm

theorem conjugate_pullbackComp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f)) (Scheme.Modules.pullbackComp f g).hom =
      (Scheme.Modules.pushforwardComp f g).inv :=
  conjugate_iso_hom_of_inv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g) (Scheme.Modules.pushforwardComp f g)
    (Scheme.Modules.conjugateEquiv_pullbackComp_inv f g)

theorem conjugate_five
    {C D : Type*} [Category C] [Category D]
    {L₀ L₁ L₂ L₃ L₄ L₅ : C ⥤ D} {R₀ R₁ R₂ R₃ R₄ R₅ : D ⥤ C}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄) (a₅ : L₅ ⊣ R₅)
    (t₁ : L₁ ⟶ L₀) (t₂ : L₂ ⟶ L₁) (t₃ : L₃ ⟶ L₂)
    (t₄ : L₄ ⟶ L₃) (t₅ : L₅ ⟶ L₄) :
    conjugateEquiv a₀ a₅ (t₅ ≫ t₄ ≫ t₃ ≫ t₂ ≫ t₁) =
      (((conjugateEquiv a₀ a₁ t₁ ≫ conjugateEquiv a₁ a₂ t₂) ≫
        conjugateEquiv a₂ a₃ t₃) ≫ conjugateEquiv a₃ a₄ t₄) ≫
          conjugateEquiv a₄ a₅ t₅ := by
  rw [← conjugateEquiv_comp a₀ a₄ a₅, ← conjugateEquiv_comp a₀ a₃ a₄,
    ← conjugateEquiv_comp a₀ a₂ a₃, ← conjugateEquiv_comp a₀ a₁ a₂]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OpenPullbackCoherence
