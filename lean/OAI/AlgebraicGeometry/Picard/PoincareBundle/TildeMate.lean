import OAI.AlgebraicGeometry.Picard.PoincareBundle.TildePullback
import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! # Tilde Mate -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeMate

noncomputable section

/-!
# The affine tilde/pullback comparison is the canonical adjunction mate
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- Uniqueness of a left adjoint after changing its right adjoint is exactly the mates isomorphism. -/
theorem leftAdjointUniq_ofNatIsoRight {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (e : R₂ ≅ R₁) :
    adj₁.leftAdjointUniq (adj₂.ofNatIsoRight e) = (conjugateIsoEquiv adj₂ adj₁).symm e := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (adj₁.homEquiv X (L₂.obj X)).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  change (adj₂.ofNatIsoRight e).unit.app X =
    adj₁.unit.app X ≫ R₁.map (((conjugateEquiv adj₂ adj₁).symm e.hom).app X)
  exact unit_conjugateEquiv_symm adj₂ adj₁ e.hom X

variable {R S : CommRingCat.{u}}

/-- The geometric affine pullback comparison has the canonical mate normalization. -/
theorem tildePullbackIso_eq_mate (f : R ⟶ S) :
    TildePullback.tildePullbackIso f =
      (conjugateIsoEquiv
        ((ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R := S)))
        ((tilde.adjunction (R := R)).comp
          (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)))).symm
        (TildePullback.pushforwardSectionsIso f).symm :=
  leftAdjointUniq_ofNatIsoRight _ _ _

/-- Equivalently, its inverse is the canonical left-adjoint composition isomorphism. -/
theorem tildePullbackIso_symm_eq_compIso (f : R ⟶ S) :
    (TildePullback.tildePullbackIso f).symm =
      Adjunction.leftAdjointCompIso (ModuleCat.extendRestrictScalarsAdj f.hom)
        (tilde.adjunction (R := S))
        ((tilde.adjunction (R := R)).comp
          (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)))
        (TildePullback.pushforwardSectionsIso f).symm := by
  rw [tildePullbackIso_eq_mate]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeMate
