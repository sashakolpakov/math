import OAI.AlgebraicGeometry.CycleClass.Thom.LocalizationStalks
import OAI.AlgebraicGeometry.CycleClass.Thom.MorphismOrderStalk
import OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule

/-! # From Stalk Order -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.FromStalkOrder.Constructions

noncomputable section

/-! The actual map from the spectrum of a stalk preserves every local
ring and coheight. Consequently it preserves original scheme orders. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.LocalizationStalks.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.MorphismOrderStalk.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (X : Scheme.{u}) (x : X)

theorem fromSpecStalk_localStalk_isIso (y : Spec (X.presheaf.stalk x)) :
    IsIso ((X.fromSpecStalk x).stalkMap y) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  let R := Γ(X, U)
  let S := X.presheaf.stalk x
  let : Algebra R S := (X.presheaf.germ U x hxU).hom.toAlgebra
  let M := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  let : IsLocalization M S := hU.isLocalization_stalk ⟨x, hxU⟩
  let l := Spec.map (X.presheaf.germ U x hxU)
  let c := hU.fromSpec
  have hl : IsIso (l.stalkMap y) := LocalizationStalks.Constructions.localizationStalkMap_isIso R S M y
  have hc : IsIso (c.stalkMap (l y)) := inferInstance
  let e := (@asIso _ _ _ _ (c.stalkMap (l y)) hc) ≪≫ (@asIso _ _ _ _ (l.stalkMap y) hl)
  have he : e.hom = (l ≫ c).stalkMap y := (Scheme.Hom.stalkMap_comp l c y).symm
  have hi : IsIso ((l ≫ c).stalkMap y) := (congrArg (fun k => IsIso k) he).mp e.isIso_hom
  exact (congrArg (fun f : Spec S ⟶ X => IsIso (f.stalkMap y))
    (hU.fromSpecStalk_eq_fromSpecStalk hxU)).mp hi

theorem fromSpecStalk_coheight (y : Spec (X.presheaf.stalk x)) :
    Order.coheight (X.fromSpecStalk x y) = Order.coheight y := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  let R := Γ(X, U)
  let S := X.presheaf.stalk x
  let : Algebra R S := (X.presheaf.germ U x hxU).hom.toAlgebra
  let M := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  let : IsLocalization M S := hU.isLocalization_stalk ⟨x, hxU⟩
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]
  change Order.coheight (hU.fromSpec ((Spec.map (X.presheaf.germ U x hxU)) y)) = _
  rw [coheight_eq_of_isOpenImmersion]
  exact LocalizationStalks.Constructions.localization_coheight R S M y

variable [IsIntegral X]

def stalkFieldMap : X.functionField ⟶ (Spec (X.presheaf.stalk x)).functionField :=
  RationalOrderTransport.Constructions.genericFieldMap (X.fromSpecStalk x) (SupportStalkModule.Constructions.genericPoint_image X x)

instance stalkFieldMap_isIso : IsIso (stalkFieldMap X x) := by
  let := fromSpecStalk_localStalk_isIso X x (genericPoint (Spec (X.presheaf.stalk x)))
  unfold stalkFieldMap RationalOrderTransport.Constructions.genericFieldMap
  infer_instance

variable [IsLocallyNoetherian X]

theorem ord_fromSpecStalk (g : X.functionField) (y : Spec (X.presheaf.stalk x)) :
    (Spec (X.presheaf.stalk x)).ord (stalkFieldMap X x g) y = X.ord g (X.fromSpecStalk x y) := by
  let := fromSpecStalk_localStalk_isIso X x y
  let : IsIso (RationalOrderTransport.Constructions.genericFieldMap (X.fromSpecStalk x) (SupportStalkModule.Constructions.genericPoint_image X x)) :=
    stalkFieldMap_isIso X x
  exact MorphismOrderStalk.Constructions.ord_of_stalkMap_isIso (X.fromSpecStalk x) (SupportStalkModule.Constructions.genericPoint_image X x)
    y (fromSpecStalk_coheight X x y) g

end

end OAI.AlgebraicGeometry.CycleClass.Thom.FromStalkOrder.Constructions
