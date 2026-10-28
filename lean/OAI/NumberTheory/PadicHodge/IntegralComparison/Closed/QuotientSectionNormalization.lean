import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.ImmersionQuotientSections

/-! # Quotient Section Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.QuotientSectionNormalization

noncomputable section

/-! The quotient presentation of closed-immersion sections is the
literal pullback of functions and commutes with actual restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem quotient_cast_inv_mk {A : Type u} [CommRing A] (I J : Ideal A) (h : I = J) (a : A) :
    (eqToIso (congrArg (fun L : Ideal A => ModuleCat.of A (A ⧸ L)) h)).inv
        (Ideal.Quotient.mk J a) = Ideal.Quotient.mk I a := by
  subst J
  rfl

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  (U : Y.Opens) (hU : IsAffineOpen U)

abbrev directImage := ImmersionQuotientSections.directImage f
abbrev ideal := f.ker.ideal ⟨U, hU⟩

def iso : (Affine.ModuleExactSections.sections U).obj (directImage f) ≅
    ModuleCat.of Γ(Y, U) (Γ(Y, U) ⧸ QuotientSectionNormalization.ideal f U hU) :=
  (ImmersionQuotientSections.quotientIso f U hU).symm ≪≫
    eqToIso (congrArg (fun I : Ideal Γ(Y, U) => ModuleCat.of Γ(Y, U) (Γ(Y, U) ⧸ I))
      (f.ker_apply ⟨U, hU⟩).symm)

theorem iso_inv_mk (a : Γ(Y, U)) :
    (iso f U hU).inv (Ideal.Quotient.mk (QuotientSectionNormalization.ideal f U hU) a) = f.app U a := by
  change (ImmersionQuotientSections.quotientIso f U hU).hom
      ((eqToIso (congrArg (fun I : Ideal Γ(Y, U) => ModuleCat.of Γ(Y, U) (Γ(Y, U) ⧸ I))
        (f.ker_apply ⟨U, hU⟩).symm)).inv (Ideal.Quotient.mk (QuotientSectionNormalization.ideal f U hU) a)) = _
  rw [quotient_cast_inv_mk (RingHom.ker (f.app U).hom) (QuotientSectionNormalization.ideal f U hU)
    (f.ker_apply ⟨U, hU⟩).symm a]
  rfl

theorem iso_pullback (a : Γ(Y, U)) :
    (iso f U hU).hom (f.app U a) = Ideal.Quotient.mk (QuotientSectionNormalization.ideal f U hU) a := by
  rw [← iso_inv_mk, Iso.inv_hom_id_apply]

def chartIso : (AffineOpen.InternalHom.sections U hU).obj (directImage f) ≅
    ModuleCat.of Γ(Y, U) (Γ(Y, U) ⧸ QuotientSectionNormalization.ideal f U hU) :=
  (Affine.ChartSections.iso U hU (directImage f)).symm ≪≫ iso f U hU

theorem chartIso_apply (m : Γ(directImage f, U)) :
    (chartIso f U hU).hom ((Affine.ChartSections.iso U hU (directImage f)).hom m) =
      (iso f U hU).hom m := by
  change (iso f U hU).hom ((Affine.ChartSections.iso U hU (directImage f)).inv
    ((Affine.ChartSections.iso U hU (directImage f)).hom m)) = _
  rw [Iso.hom_inv_id_apply]

theorem chartIso_inv_mk (a : Γ(Y, U)) :
    (chartIso f U hU).inv (Ideal.Quotient.mk (QuotientSectionNormalization.ideal f U hU) a) =
      (Affine.ChartSections.iso U hU (directImage f)).hom (f.app U a) := by
  change (Affine.ChartSections.iso U hU (directImage f)).hom
    ((iso f U hU).inv (Ideal.Quotient.mk (QuotientSectionNormalization.ideal f U hU) a)) = _
  rw [iso_inv_mk]

variable (V : Y.Opens) (hV : IsAffineOpen V) (i : V ⟶ U)

def quotientRestriction : (Γ(Y, U) ⧸ QuotientSectionNormalization.ideal f U hU) →+* (Γ(Y, V) ⧸ QuotientSectionNormalization.ideal f V hV) :=
  Ideal.quotientMap (QuotientSectionNormalization.ideal f V hV) (Y.presheaf.map i.op).hom
    (f.ker.ideal_le_comap_ideal (U := ⟨V, hV⟩) (V := ⟨U, hU⟩) i.le)

theorem restriction (m : Γ(directImage f, U)) :
    (iso f V hV).hom ((directImage f).presheaf.map i.op m) =
      quotientRestriction f U hU V hV i ((iso f U hU).hom m) := by
  obtain ⟨a, rfl⟩ := f.app_surjective U hU m
  have h : (directImage f).presheaf.map i.op (f.app U a) = f.app V (Y.presheaf.map i.op a) :=
    (ConcreteCategory.congr_hom (f.naturality i.op) a).symm
  rw [h, iso_pullback, iso_pullback]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.QuotientSectionNormalization
