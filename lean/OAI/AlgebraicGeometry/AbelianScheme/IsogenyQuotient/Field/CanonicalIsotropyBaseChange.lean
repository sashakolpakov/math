import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.CanonicalPairingBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.KernelBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.StandardWeilIsotropy
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.WeilIsotropy

/-! # Canonical Isotropy Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.CanonicalIsotropyBaseChange.Construction

noncomputable section

/-! Intrinsic full-scheme self-annihilation over the original field
implies PoincareBundle's full geometric Weil criterion. No compatibility assumption
or restriction to geometric points is introduced. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {k : Type} [Field k] {g : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (n : ℕ) (hn : 0 < n)
  (hker : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)
  (hlag :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.hom)
    (PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).relativeAnnihilator F = F)

include hker hlag in
set_option backward.isDefEq.respectTransparency false in
theorem canonicalKernel_geometric_standardWeil_selfAnnihilating :
    Picard.PoincareBundle.Geometric.WeilIsotropy.SelfAnnihilating D pol f n hn hker := by
  intro K _ _ s
  have hl := Intrinsic.KernelBaseChange.Construction.nativeMorphismKernel_self_annihilating_baseChange
    (Grp.mk A.scheme) (Grp.mk B.scheme) (Over.mk s) (Grp.homMk f.hom) n
    (PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn) hlag
  have he := CanonicalPairingBaseChange.Construction.fieldNativePolarizationPairing_baseChange D pol n hn s
  let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback s).scheme n)
    (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (f.pullback s).hom)
  have hfield : (PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.pullback s) (D.pullback s)
      (pol.pullback s) n hn).relativeAnnihilator F = F :=
    (congrArg (fun e => e.relativeAnnihilator F) he).trans hl
  exact Canonical.StandardWeilIsotropy.Construction.canonicalKernel_standardWeil_selfAnnihilating (D.pullback s) (pol.pullback s) n hn
    (f.pullback s).hom (Picard.PoincareBundle.Kernel.ContainmentBaseChange.contained f n hker s) hfield

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.CanonicalIsotropyBaseChange.Construction
