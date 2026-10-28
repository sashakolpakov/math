import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OpenPullbackCoherence

/-! # Open Square -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OpenSquare

noncomputable section

/-! Identifying the standard geometric open pullback square with its
adjoint construction, by the native composition laws. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OpenPullbackCoherence

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

theorem canonical_conjugate :
    conjugateEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
        (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι))
      ((Scheme.Modules.restrictAdjunction U.ι).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)))
      (Picard.PoincareBundle.Open.BaseChange.pullbackRestrictIso f U).inv =
        (Picard.PoincareBundle.Open.Adjunction.pushforwardSquareIso f U).hom := by
  let af := Scheme.Modules.pullbackPushforwardAdjunction f
  let ag := Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)
  let ax := Scheme.Modules.pullbackPushforwardAdjunction (f ⁻¹ᵁ U).ι
  let ay := Scheme.Modules.pullbackPushforwardAdjunction U.ι
  let rx := Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι
  let ry := Scheme.Modules.restrictAdjunction U.ι
  let ac := Scheme.Modules.pullbackPushforwardAdjunction ((f ⁻¹ᵁ U).ι ≫ f)
  let ad := Scheme.Modules.pullbackPushforwardAdjunction ((f ∣_ U) ≫ U.ι)
  let tx := Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι
  let ty := Scheme.Modules.restrictFunctorIsoPullback U.ι
  let t₁ := Functor.whiskerLeft (Scheme.Modules.pullback f) tx.inv
  let t₂ := (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).inv
  let t₃ := (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).inv
  let t₄ := (Scheme.Modules.pullbackComp (f ∣_ U) U.ι).hom
  let t₅ := Functor.whiskerRight ty.hom (Scheme.Modules.pullback (f ∣_ U))
  have h₁ : conjugateEquiv (af.comp rx) (af.comp ax) t₁ = 𝟙 _ := by
    change conjugateEquiv (af.comp rx) (af.comp ax)
      (Functor.whiskerLeft (Scheme.Modules.pullback f) (rx.leftAdjointUniq ax).inv) = _
    rw [conjugateEquiv_whiskerLeft, OpenPullbackCoherence.conjugate_leftAdjointUniq_inv]
    exact Functor.whiskerRight_id _
  have h₅ : conjugateEquiv (ay.comp ag) (ry.comp ag) t₅ = 𝟙 _ := by
    change conjugateEquiv (ay.comp ag) (ry.comp ag)
      (Functor.whiskerRight (ry.leftAdjointUniq ay).hom (Scheme.Modules.pullback (f ∣_ U))) = _
    rw [conjugateEquiv_whiskerRight, OpenPullbackCoherence.conjugate_leftAdjointUniq_hom]
    exact Functor.whiskerLeft_id _
  have h₂ : conjugateEquiv (af.comp ax) ac t₂ =
      (Scheme.Modules.pushforwardComp (f ⁻¹ᵁ U).ι f).hom :=
    Scheme.Modules.conjugateEquiv_pullbackComp_inv (f ⁻¹ᵁ U).ι f
  have h₃ : conjugateEquiv ac ad t₃ =
      (Scheme.Modules.pushforwardCongr (morphismRestrict_ι f U).symm).hom :=
    OpenPullbackCoherence.conjugate_pullbackCongr_inv (morphismRestrict_ι f U).symm
  have h₄ : conjugateEquiv ad (ay.comp ag) t₄ =
      (Scheme.Modules.pushforwardComp (f ∣_ U) U.ι).inv :=
    OpenPullbackCoherence.conjugate_pullbackComp_hom (f ∣_ U) U.ι
  have hc := OpenPullbackCoherence.conjugate_five (af.comp rx) (af.comp ax) ac ad (ay.comp ag) (ry.comp ag)
    t₁ t₂ t₃ t₄ t₅
  change conjugateEquiv (af.comp rx) (ry.comp ag) (t₅ ≫ t₄ ≫ t₃ ≫ t₂ ≫ t₁) = _
  rw [hc, h₁, h₂, h₃, h₄, h₅, Category.id_comp, Category.comp_id]
  rfl

theorem canonical_eq_adjoint :
    (Picard.PoincareBundle.Open.BaseChange.pullbackRestrictIso f U).symm =
      Picard.PoincareBundle.Open.Adjunction.adjointPullbackSquare f U := by
  apply Iso.ext
  apply (conjugateEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
        (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι))
      ((Scheme.Modules.restrictAdjunction U.ι).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)))).injective
  exact (canonical_conjugate f U).trans
    ((conjugateEquiv _ _).apply_symm_apply (Picard.PoincareBundle.Open.Adjunction.pushforwardSquareIso f U).hom).symm

theorem canonical_rightMate_isIso :
    IsIso (Picard.PoincareBundle.DescentRestriction.rightMate
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))
      (Picard.PoincareBundle.Open.BaseChange.pullbackRestrictIso f U).symm) := by
  rw [canonical_eq_adjoint]
  exact Picard.PoincareBundle.Open.Adjunction.rightMate_isIso f U

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OpenSquare
