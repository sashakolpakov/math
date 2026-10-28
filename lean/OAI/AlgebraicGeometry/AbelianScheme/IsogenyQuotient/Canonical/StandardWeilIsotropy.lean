import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.StandardWeilValue
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PolarizationAlternating
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlternatingOrthogonality
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.BundleSelfAnnihilator

/-! # Standard Weil Isotropy -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.StandardWeilIsotropy.Construction

noncomputable section

/-! Full self-annihilation agrees between the actual canonical CartierDuality
polarization pairing and PoincareBundle's standard Weil group-scheme pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (n : ℕ) (hn : 0 < n)

theorem canonicalStandardWeilValue_eq_one_iff (T : Over (Spec (.of k)))
    (x y : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    Picard.PoincareBundle.Canonical.WeilData.value D pol.isogeny n hn x y = 1 ↔
      (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).pairValue x y = 1 := by
  rw [StandardWeilValue.Construction.canonicalStandardWeilValue_eq]
  have hc := (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).alternating_pairValue_eq_one_comm
    (IsogenyQuotient.Field.PolarizationAlternating.Construction.fieldNativePolarizationPairing_alternating D pol n hn) T x y
  constructor
  · intro h
    exact hc.mpr (congrArg ULift.down h)
  · intro h
    exact congrArg ULift.up (hc.mp h)

theorem canonicalStandardWeil_selfAnnihilating_iff
    {H : Over (Spec (.of k))} [GrpObj H] (i : H ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) [IsMonHom i] :
    Picard.PoincareBundle.Canonical.WeilData.SelfAnnihilating D pol.isogeny n hn i ↔
      (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).relativeAnnihilator (Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i) =
        Intrinsic.RelativeAnnihilator.Construction.nativeImageRelativeSubgroup i := by
  let e := IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn
  have hv (T : Over (Spec (.of k))) (y : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
      (∀ (U : Over (Spec (.of k))) (a : U ⟶ T) (x : U ⟶ H),
        Picard.PoincareBundle.Canonical.WeilData.value D pol.isogeny n hn (x ≫ i) (a ≫ y) = 1) ↔
      ∀ (U : Over (Spec (.of k))) (a : U ⟶ T) (x : U ⟶ H), e.pairValue (x ≫ i) (a ≫ y) = 1 := by
    apply forall_congr'
    intro U
    apply forall_congr'
    intro a
    apply forall_congr'
    intro x
    exact canonicalStandardWeilValue_eq_one_iff D pol n hn U (x ≫ i) (a ≫ y)
  constructor
  · intro h
    ext T t y
    rw [e.nativeImage_annihilator_membership]
    exact (hv T y).symm.trans (h T y)
  · intro h T y
    let t : T ⟶ Over.mk (𝟙 (Spec (.of k))) := Over.homMk T.hom (Category.comp_id _)
    have hm := e.nativeImage_annihilator_membership i T t y
    rw [h] at hm
    exact (hv T y).trans hm.symm

set_option backward.isDefEq.respectTransparency false in
theorem canonicalKernel_standardWeil_selfAnnihilating
    {B : Over (Spec (.of k))} [GrpObj B] (f : A.scheme ⟶ B) [IsMonHom f]
    (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f = 1 → x ^ n = 1)
    (hlag :
      let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f)
      (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).relativeAnnihilator F = F) :
    Picard.PoincareBundle.Canonical.WeilData.SelfAnnihilating D pol.isogeny n hn
      (Picard.PoincareBundle.Kernel.ContainmentMap.torsionMap f n hf) := by
  apply (canonicalStandardWeil_selfAnnihilating_iff D pol n hn _).mpr
  rw [← Poincare.BundleSelfAnnihilator.Construction.nativeTorsion_kernel_eq_e45_image f n hf]
  exact hlag

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.StandardWeilIsotropy.Construction
