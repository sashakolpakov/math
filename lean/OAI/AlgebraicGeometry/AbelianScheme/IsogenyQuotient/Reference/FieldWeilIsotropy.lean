import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.FieldAlternation
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlternatingOrthogonality
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.Bundle

/-! # Field Weil Isotropy -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.FieldWeilIsotropy.Construction

noncomputable section

/-! The intrinsic native self-annihilator gives the accepted PoincareBundle
original-field Weil criterion on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {k : Type} [Field k] {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
  (n : ℕ) (hn : 0 < n)

theorem originalFieldWeilValue_eq_one_iff (T : Over (Spec (.of k)))
    (x y : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    Picard.PoincareBundle.Field.WeilPairing.value D pol.isogeny n hn
      (x ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n)
      (Picard.PoincareBundle.Field.WeilCanonicalComparison.kernel_torsion A.scheme n x)
      (y ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n)
      (Picard.PoincareBundle.Field.WeilCanonicalComparison.kernel_torsion A.scheme n y) = 1 ↔
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).pairValue x y = 1 := by
  rw [← IsogenyQuotient.Field.WeilCharacterValue.Construction.fieldNativePolarizationPairing_character_value]
  have hu := map_eq_one_iff (x := (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).pairValue y x)
    (CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T)
    (CartierDuality.UnitValueDetection.Construction.Schemes.multiplicativeGroupUnitHom_injective T)
  exact hu.trans ((IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).alternating_pairValue_eq_one_comm
    (FieldAlternation.Construction.fieldNativePolarizationPairing_alternating_original D pol n hn) T y x)

set_option backward.isDefEq.respectTransparency false in
theorem canonicalKernel_originalFieldWeil_selfAnnihilating
    {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
    (hker : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme),
      x ≫ f.hom = 1 → x ^ n = 1)
    (hlag :
      let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.hom)
      (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).relativeAnnihilator F = F)
    (T : Over (Spec (.of k))) (y : T ⟶ A.scheme) (hy : y ^ n = 1) :
    (∀ (U : Over (Spec (.of k))) (b : U ⟶ T) (x : U ⟶ A.scheme) (hx : x ≫ f.hom = 1),
      Picard.PoincareBundle.Field.WeilPairing.value D pol.isogeny n hn x (hker U x hx) (b ≫ y)
        (by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) = 1) ↔ y ≫ f.hom = 1 := by
  let e := IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn
  let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.hom)
  let t : T ⟶ Over.mk (𝟙 (Spec (.of k))) := Over.homMk T.hom (Category.comp_id _)
  let z := Torsion.Groups.Construction.nativeTorsionLift A.scheme n y hy
  have hz : z ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n = y := Torsion.Groups.Construction.nativeTorsionLift_inclusion _ _ _ _
  have hm : z ∈ (e.relativeAnnihilator F).points T t ↔ y ≫ f.hom = 1 := by
    rw [show e.relativeAnnihilator F = F from hlag]
    change (z ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n) ≫ f.hom = 1 ↔ _
    rw [hz]
  rw [← hm]
  constructor
  · intro h U b x hx
    have hv := h U b (x ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n) hx
    have hc := originalFieldWeilValue_eq_one_iff D pol n hn U x (b ≫ z)
    simp only [Category.assoc, hz] at hc
    exact hc.mp hv
  · intro h U b x hx
    let w := Torsion.Groups.Construction.nativeTorsionLift A.scheme n x (hker U x hx)
    have hw : w ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n = x := Torsion.Groups.Construction.nativeTorsionLift_inclusion _ _ _ _
    have hf : w ∈ F.points U (b ≫ t) := by
      change (w ≫ Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n) ≫ f.hom = 1
      rw [hw]
      exact hx
    have hv := h U b w hf
    have hc := originalFieldWeilValue_eq_one_iff D pol n hn U w (b ≫ z)
    simp only [hw, Category.assoc, hz] at hc
    exact hc.mpr hv

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.FieldWeilIsotropy.Construction
