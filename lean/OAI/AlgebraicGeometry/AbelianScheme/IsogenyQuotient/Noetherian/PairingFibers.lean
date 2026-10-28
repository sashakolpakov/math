import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PairingBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionPairingBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingBaseChangeFlip
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.KernelBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PolarizationAdapter

/-! # Pairing Fibers -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PairingFibers.Construction

noncomputable section

/-! The relative canonical pairing specializes to the original field
pairing, retaining full scheme-theoretic kernel self-annihilation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} [IsLocallyNoetherian S] {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (n : ℕ) (hn : 0 < n)

set_option backward.isDefEq.respectTransparency false in
theorem noetherianNativePolarizationPairing_baseChange
    {S' : Scheme} [IsLocallyNoetherian S'] (s : S' ⟶ S) :
    PolarizationAdapter.Construction.noetherianNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) n hn =
      Intrinsic.TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback s (Grp.mk A.scheme) (Grp.mk A.scheme) n
        (PolarizationAdapter.Construction.noetherianNativePolarizationPairing A D pol n hn) := by
  apply Annihilator.Construction.SchemeBicharacter.eq_of_pairValue_eq
  intro T x y
  exact (PairingBaseChange.Construction.noetherianNativePolarizationPairing_baseChange_value D pol n hn s T x y).trans
    (Intrinsic.TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback_value s (Grp.mk A.scheme) (Grp.mk A.scheme) n
      (PolarizationAdapter.Construction.noetherianNativePolarizationPairing A D pol n hn) T x y).symm

set_option backward.isDefEq.respectTransparency false in
theorem noetherianCanonicalKernel_geometric_selfAnnihilating
    {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
    (hlag :
      let H := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.hom)
      (PolarizationAdapter.Construction.noetherianNativePolarizationPairing A D pol n hn).relativeAnnihilator H = H)
    (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) :
    let H := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback s).scheme n)
      (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (f.pullback s).hom)
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) n hn).relativeAnnihilator H = H := by
  have he := noetherianNativePolarizationPairing_baseChange D pol n hn s
  have hl := Intrinsic.KernelBaseChange.Construction.nativeMorphismKernel_self_annihilating_baseChange
    (Grp.mk A.scheme) (Grp.mk B.scheme) (Over.mk s) (Grp.homMk f.hom) n
    (PolarizationAdapter.Construction.noetherianNativePolarizationPairing A D pol n hn) hlag
  let H := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback s).scheme n)
    (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (f.pullback s).hom)
  exact (congrArg (fun e => e.relativeAnnihilator H) he).trans hl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PairingFibers.Construction
