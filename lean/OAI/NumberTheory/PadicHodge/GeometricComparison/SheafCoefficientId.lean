import OAI.NumberTheory.PadicHodge.PeriodInvariants.SheafificationCoherence

/-! # Sheaf Coefficient Id -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SheafCoefficientId.SheafCoefficientIdentity

noncomputable section

/-! Canonical sheafification coefficient comparisons are identities for the identity functor. -/

open _root_.CategoryTheory

variable {C A : Type*} [Category* C] [Category* A]
  (J : GrothendieckTopology C) [HasWeakSheafify J A]

theorem sheafComposeNatIso_id (P : Cᵒᵖ ⥤ A) :
    (sheafComposeNatIso J (𝟭 A) (sheafificationAdjunction J A) (sheafificationAdjunction J A)).app P =
      Iso.refl ((presheafToSheaf J A).obj P) := by
  apply Iso.ext
  apply ((sheafificationAdjunction J A).homEquiv P _).injective
  have h := sheafComposeNatTrans_fac J (𝟭 A) (sheafificationAdjunction J A)
    (sheafificationAdjunction J A) P
  exact h.trans ((sheafificationAdjunction J A).homEquiv_id P).symm

theorem constantCommuteCompose_id (a : A) :
    (constantCommuteCompose J (𝟭 A)).app a = Iso.refl ((constantSheaf J A).obj a) := by
  change ((sheafComposeNatIso J (𝟭 A) (sheafificationAdjunction J A)
    (sheafificationAdjunction J A)).app ((Functor.const Cᵒᵖ).obj a)).symm ≪≫
      (presheafToSheaf J A).mapIso (Functor.constComp Cᵒᵖ a (𝟭 A)).symm = _
  rw [sheafComposeNatIso_id]
  change Iso.refl _ ≪≫ (presheafToSheaf J A).mapIso (Iso.refl _) = _
  rw [Functor.mapIso_refl, Iso.refl_trans]
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SheafCoefficientId.SheafCoefficientIdentity
