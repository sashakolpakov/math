import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeMate
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Composition

/-! # Mate Normalization -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

noncomputable section

/-!
# The invariant comparison uses the standard geometric Čech gluing
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem leftAdjointUniq_symm {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R : D ⥤ C} (a : L₁ ⊣ R) (b : L₂ ⊣ R) :
    (a.leftAdjointUniq b).symm = b.leftAdjointUniq a := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact Adjunction.leftAdjointUniq_inv_app a b X

/-- Changing the right adjoint on the source gives the same canonical mate normalization. -/
theorem leftAdjointUniq_ofNatIsoRight_left {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : R₁ ≅ R₂) :
    (a.ofNatIsoRight e).leftAdjointUniq b = (conjugateIsoEquiv b a).symm e.symm := by
  calc
    _ = (b.leftAdjointUniq (a.ofNatIsoRight e)).symm :=
      (leftAdjointUniq_symm b (a.ofNatIsoRight e)).symm
    _ = ((conjugateIsoEquiv a b).symm e).symm :=
      congrArg Iso.symm (TildeMate.leftAdjointUniq_ofNatIsoRight b a e)
    _ = _ := rfl

/-- The forward geometric pullback composition has the inverse direct-image comparison as mate. -/
theorem conjugate_pullbackComp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f)) (Scheme.Modules.pullbackComp f g).hom =
      (Scheme.Modules.pushforwardComp f g).inv := by
  have h : conjugateIsoEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f))
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
      (Scheme.Modules.pullbackComp f g).symm = Scheme.Modules.pushforwardComp f g :=
    Iso.ext (Scheme.Modules.conjugateEquiv_pullbackComp_inv f g)
  exact congrArg Iso.inv h

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p q : Z ⟶ X) (h : p ≫ f = q ≫ f)

/-- The usual scheme pullback-composition path between the two projections. -/
def standardGluing : Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback p ≅
    Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback q :=
  Scheme.Modules.pullbackComp p f ≪≫ Scheme.Modules.pullbackCongr h ≪≫
    (Scheme.Modules.pullbackComp q f).symm

theorem standardGluing_mate :
    conjugateEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
        (Scheme.Modules.pullbackPushforwardAdjunction p))
      ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
        (Scheme.Modules.pullbackPushforwardAdjunction q)) (standardGluing f p q h).inv =
      (Geometric.CechInvariant.directImageIso f p q h).hom := by
  change conjugateEquiv _ _ ((Scheme.Modules.pullbackComp q f).hom ≫
    (Scheme.Modules.pullbackCongr h).inv ≫ (Scheme.Modules.pullbackComp p f).inv) = _
  rw [← conjugateEquiv_comp _ (Scheme.Modules.pullbackPushforwardAdjunction (q ≫ f)),
    ← conjugateEquiv_comp _ (Scheme.Modules.pullbackPushforwardAdjunction (p ≫ f)),
    Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    Affine.Composition.pullbackCongr_mate, conjugate_pullbackComp_hom]
  exact Category.assoc _ _ _

/-- The comparison chosen by the invariant construction is the standard geometric one. -/
theorem pullbackIso_eq_standard : Geometric.CechInvariant.pullbackIso f p q h = standardGluing f p q h := by
  have hm := leftAdjointUniq_ofNatIsoRight_left
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction p))
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction q)) (Geometric.CechInvariant.directImageIso f p q h)
  change Geometric.CechInvariant.pullbackIso f p q h = _ at hm
  rw [hm]
  apply Iso.ext_inv
  apply (conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction p))
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction q))).injective
  change (conjugateEquiv _ _) ((conjugateEquiv _ _).symm (Geometric.CechInvariant.directImageIso f p q h).hom) = _
  rw [Equiv.apply_symm_apply]
  exact (standardGluing_mate f p q h).symm

variable (M : X.Modules)
  (σ : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback q).obj M)

/-- The invariant comparison satisfies the ordinary geometric gluing diagram. -/
theorem comparison_standard_compatible :
    (Scheme.Modules.pullback p).map (Geometric.CechInvariant.comparison f p q h M σ) ≫ σ.hom =
      (standardGluing f p q h).hom.app (Geometric.CechInvariant.invariantSheaf f p q h M σ) ≫
        (Scheme.Modules.pullback q).map (Geometric.CechInvariant.comparison f p q h M σ) := by
  rw [← pullbackIso_eq_standard]
  exact Geometric.CechInvariant.comparison_compatible f p q h M σ

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization
