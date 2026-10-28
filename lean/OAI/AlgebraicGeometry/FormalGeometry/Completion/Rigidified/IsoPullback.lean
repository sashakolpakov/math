import OAI.AlgebraicGeometry.FormalGeometry.Completion.RigidificationComparisonPasting

/-! # Iso Pullback -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.IsoPullback

noncomputable section

/-! Normalized line comparisons retain their axis value under actual
module pullback, with all composition comparisons included. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

namespace Construction

universe u

@[reassoc]
theorem pullbackSquare_naturality {Y Z T U : Scheme.{u}}
    (j : Z ⟶ Y) (b : T ⟶ Y) (c : U ⟶ Z) (t : U ⟶ T) (h : c ≫ j = t ≫ b)
    {L M : Y.Modules} (e : L ⟶ M) :
    (Scheme.Modules.pullback c).map ((Scheme.Modules.pullback j).map e) ≫
        (Quotients.FiniteDescent.PullbackSectionCongr.Construction.PullbackSectionSquare.iso j b c t h M).hom =
      (Quotients.FiniteDescent.PullbackSectionCongr.Construction.PullbackSectionSquare.iso j b c t h L).hom ≫
        (Scheme.Modules.pullback t).map ((Scheme.Modules.pullback b).map e) := by
  let α := Scheme.Modules.pullbackComp c j ≪≫ Scheme.Modules.pullbackCongr h ≪≫
    (Scheme.Modules.pullbackComp t b).symm
  exact α.hom.naturality e

def compositeLineIso {X Y Z : Scheme.{u}} (f₁ f₂ : Y ⟶ X) (j : Z ⟶ Y)
    (M : X.Modules)
    (e : (Scheme.Modules.pullback f₁).obj M ≅ (Scheme.Modules.pullback f₂).obj M) :
    (Scheme.Modules.pullback (j ≫ f₁)).obj M ≅ (Scheme.Modules.pullback (j ≫ f₂)).obj M :=
  ((Scheme.Modules.pullbackComp j f₁).app M).symm ≪≫
    (Scheme.Modules.pullback j).mapIso e ≪≫ (Scheme.Modules.pullbackComp j f₂).app M

theorem compositeLineIso_normalized
    {X Y Z S T U : Scheme.{u}} (f₁ f₂ : Y ⟶ X) (j : Z ⟶ Y)
    (s : S ⟶ X) (b : T ⟶ Y) (g₁ g₂ : T ⟶ S) (c : U ⟶ Z) (t : U ⟶ T)
    (h : c ≫ j = t ≫ b) (h₁ : b ≫ f₁ = g₁ ≫ s) (h₂ : b ≫ f₂ = g₂ ≫ s)
    (h₁' : c ≫ (j ≫ f₁) = (t ≫ g₁) ≫ s)
    (h₂' : c ≫ (j ≫ f₂) = (t ≫ g₂) ≫ s)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (e : (Scheme.Modules.pullback f₁).obj M ≅ (Scheme.Modules.pullback f₂).obj M)
    (he : (Scheme.Modules.pullback b).map e.hom ≫
      (FrameScalar.Construction.rigidificationBaseChangeIso f₂ b g₂ s h₂ M r).hom =
        (FrameScalar.Construction.rigidificationBaseChangeIso f₁ b g₁ s h₁ M r).hom) :
    (Scheme.Modules.pullback c).map (compositeLineIso f₁ f₂ j M e).hom ≫
      (FrameScalar.Construction.rigidificationBaseChangeIso (j ≫ f₂) c (t ≫ g₂) s h₂' M r).hom =
        (FrameScalar.Construction.rigidificationBaseChangeIso (j ≫ f₁) c (t ≫ g₁) s h₁' M r).hom := by
  apply (cancel_epi ((Scheme.Modules.pullback c).map ((Scheme.Modules.pullbackComp j f₁).hom.app M))).mp
  simp only [compositeLineIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, (Scheme.Modules.pullback c).map_id, Category.id_comp]
  rw [RigidificationComparisonPasting.Construction.rigidificationBaseChangeIso_paste f₂ j s b g₂ c t h h₂ h₂' M r,
    RigidificationComparisonPasting.Construction.rigidificationBaseChangeIso_paste f₁ j s b g₁ c t h h₁ h₁' M r,
    pullbackSquare_naturality_assoc]
  rw [← Functor.map_comp_assoc, he]

def lineIsoPullbackTo {X Y Z : Scheme.{u}} (f₁ f₂ : Y ⟶ X) (j : Z ⟶ Y)
    (f₁' f₂' : Z ⟶ X) (hj₁ : j ≫ f₁ = f₁') (hj₂ : j ≫ f₂ = f₂') (M : X.Modules)
    (e : (Scheme.Modules.pullback f₁).obj M ≅ (Scheme.Modules.pullback f₂).obj M) :
    (Scheme.Modules.pullback f₁').obj M ≅ (Scheme.Modules.pullback f₂').obj M :=
  ((Scheme.Modules.pullbackComp j f₁ ≪≫ Scheme.Modules.pullbackCongr hj₁).app M).symm ≪≫
    (Scheme.Modules.pullback j).mapIso e ≪≫
      (Scheme.Modules.pullbackComp j f₂ ≪≫ Scheme.Modules.pullbackCongr hj₂).app M

theorem lineIsoPullbackTo_normalized
    {X Y Z S T U : Scheme.{u}} (f₁ f₂ : Y ⟶ X) (j : Z ⟶ Y)
    (f₁' f₂' : Z ⟶ X) (hj₁ : j ≫ f₁ = f₁') (hj₂ : j ≫ f₂ = f₂')
    (s : S ⟶ X) (b : T ⟶ Y) (g₁ g₂ : T ⟶ S) (c : U ⟶ Z) (t : U ⟶ T)
    (h : c ≫ j = t ≫ b) (h₁ : b ≫ f₁ = g₁ ≫ s) (h₂ : b ≫ f₂ = g₂ ≫ s)
    (h₁' : c ≫ f₁' = (t ≫ g₁) ≫ s) (h₂' : c ≫ f₂' = (t ≫ g₂) ≫ s)
    (M : X.Modules) (r : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)
    (e : (Scheme.Modules.pullback f₁).obj M ≅ (Scheme.Modules.pullback f₂).obj M)
    (he : (Scheme.Modules.pullback b).map e.hom ≫
      (FrameScalar.Construction.rigidificationBaseChangeIso f₂ b g₂ s h₂ M r).hom =
        (FrameScalar.Construction.rigidificationBaseChangeIso f₁ b g₁ s h₁ M r).hom) :
    (Scheme.Modules.pullback c).map (lineIsoPullbackTo f₁ f₂ j f₁' f₂' hj₁ hj₂ M e).hom ≫
      (FrameScalar.Construction.rigidificationBaseChangeIso f₂' c (t ≫ g₂) s h₂' M r).hom =
        (FrameScalar.Construction.rigidificationBaseChangeIso f₁' c (t ≫ g₁) s h₁' M r).hom := by
  subst f₁'
  subst f₂'
  simpa only [lineIsoPullbackTo, compositeLineIso, Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_refl]
    using compositeLineIso_normalized f₁ f₂ j s b g₁ g₂ c t h h₁ h₂ h₁' h₂' M r e he

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.IsoPullback
