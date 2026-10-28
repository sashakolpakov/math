import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Ideal
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ProductPullback

/-! # Center Permissibility -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.CenterPermissibility.Construction

noncomputable section

/-! A blowup preserves the prescribed order along every disjoint remaining center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem ideal_colon_eq_of_sup_top {R : Type u} [CommRing R]
    (I J : Ideal R) (h : I ⊔ J = ⊤) : I.colon (J : Set R) = I := by
  apply le_antisymm ?_ Ideal.le_colon
  intro x hx
  have hone : (1 : R) ∈ I ⊔ J := by rw [h]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hone
  have hxb : x * b ∈ I := (Submodule.mem_colon.mp hx) b hb
  have hxone : x * (a + b) ∈ I := by
    rw [mul_add]
    exact I.add_mem (I.mul_mem_left x ha) hxb
  simpa only [hab, mul_one] using hxone

theorem ideal_power_colon_eq_of_sup_top {R : Type u} [CommRing R]
    (I J : Ideal R) (a b : ℕ) (h : I ⊔ J = ⊤) :
    (I ^ a).colon ((J ^ b : Ideal R) : Set R) = I ^ a :=
  ideal_colon_eq_of_sup_top _ _
    (Ideal.isCoprime_iff_sup_eq.mp ((Ideal.isCoprime_iff_sup_eq.mpr h).pow (m := a) (n := b)))

theorem controlledIdealSheaf_le_disjoint_center_power
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (K L J : X.IdealSheafData) (π : Y ⟶ X) (b c : ℕ)
    (hdisjoint : L ⊔ K = ⊤) (hJ : J ≤ L ^ c) :
    GlobalControlled.Ideal.Construction.controlledIdealSheaf K J b π ≤ (L.comap π) ^ c := by
  have hmap := Scheme.IdealSheafData.comap_mono π hJ
  change J.comap π ≤ (L ^ c).comap π at hmap
  rw [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow] at hmap
  have hdis : L.comap π ⊔ K.comap π = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_sup, hdisjoint, Scheme.IdealSheafData.comap_top]
  intro U
  change ((J.comap π).ideal U).colon (((K.comap π).ideal U ^ b : Ideal Γ(Y, U)) : Set Γ(Y, U)) ≤
    (L.comap π).ideal U ^ c
  have h := Submodule.colon_mono (hmap U) (le_refl (((K.comap π).ideal U ^ b : Ideal Γ(Y, U)) : Set Γ(Y, U)))
  change ((J.comap π).ideal U).colon (((K.comap π).ideal U ^ b : Ideal Γ(Y, U)) : Set Γ(Y, U)) ≤
    ((L.comap π).ideal U ^ c).colon (((K.comap π).ideal U ^ b : Ideal Γ(Y, U)) : Set Γ(Y, U)) at h
  have hd := congrArg (fun A : Y.IdealSheafData => A.ideal U) hdis
  rw [ideal_power_colon_eq_of_sup_top _ _ c b hd] at h
  exact h

theorem globalBlowup_preserves_disjoint_center_permissibility
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (K L J : X.IdealSheafData) (hK : K ≠ ⊥) (b c : ℕ)
    (hdisjoint : L ⊔ K = ⊤) (hJ : J ≤ L ^ c) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal K J hK b ≤ (L.comap (GlobalBlowup.Data.Construction.globalBlowupToBase K hK)) ^ c :=
  controlledIdealSheaf_le_disjoint_center_power K L J (GlobalBlowup.Data.Construction.globalBlowupToBase K hK) b c hdisjoint hJ

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Disjoint.CenterPermissibility.Construction
