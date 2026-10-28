import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Nilpotent Open Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentOpenRestriction

noncomputable section

/-! Global nilpotence of the actual closed-immersion ideal is
preserved on every open restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
  (hi : IsNilpotent i.ker)

include hi in
theorem nilpotent (U : Y.Opens) : IsNilpotent (i ∣_ U).ker := by
  obtain ⟨N, hN⟩ := hi
  refine ⟨N, Scheme.IdealSheafData.ext ?_⟩
  funext V
  change ((i ∣_ U).ker.ideal V) ^ N = ⊥
  rw [Scheme.ker_morphismRestrict_ideal]
  exact congrArg (fun I : Y.IdealSheafData =>
    I.ideal ⟨U.ι ''ᵁ V, V.2.image_of_isOpenImmersion _⟩) hN

include hi in
theorem nilpotent_of_isPullback {X' Y' : Scheme.{u}}
    (i' : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y) [IsOpenImmersion b]
    (hp : IsPullback i' a b i) : IsNilpotent i'.ker := by
  obtain ⟨N, hN⟩ := hi
  refine ⟨N, Scheme.IdealSheafData.ext ?_⟩
  funext U
  change (i'.ker.ideal U) ^ N = ⊥
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion i i' a b hp]
  apply le_antisymm _ bot_le
  apply (Ideal.le_comap_pow (b.appIso U).inv.hom N).trans
  have hpow : (i.ker.ideal ⟨b ''ᵁ U, U.2.image_of_isOpenImmersion _⟩) ^ N = ⊥ :=
    congrArg (fun I : Y.IdealSheafData => I.ideal ⟨b ''ᵁ U, U.2.image_of_isOpenImmersion _⟩) hN
  rw [hpow]
  intro x hx
  exact (ConcreteCategory.bijective_of_isIso (b.appIso U).inv).injective
    (hx.trans ((b.appIso U).inv.hom.map_zero).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentOpenRestriction
