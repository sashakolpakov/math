import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.DualExistence
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.StandardWeilIsotropy
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SharedDualMapComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilPolarizationDescent

/-! # Polarization Existence -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PolarizationExistence.Construction

noncomputable section

/-! Full canonical isotropy constructs both the quotient dual and its
actual positive polarization of unchanged type, with the exact pullback identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

variable {S : Scheme} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
  (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) (n : ℕ) (hn : 0 < n)
  {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (A.pullback s) B)
  (hker : ∀ (T : Over (Spec (.of k))) (x : T ⟶ (A.pullback s).scheme), x ≫ f.hom = 1 → x ^ n = 1)
  (hlag :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback s).scheme n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.hom)
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) n hn).relativeAnnihilator F = F)

include hker hlag in
set_option backward.isDefEq.respectTransparency false in
theorem geometricCanonicalQuotient_polarization_exists (hc : Nat.Coprime n ((∏ j, δ j) ^ 2)) :
    ∃ (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) (p : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δ),
      f.hom ≫ p.isogeny.hom ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom (D.pullback s) DB =
        (Geometric.PoincareSymmetry.Construction.geometricPolarizationMap D pol k s) ^ n := by
  obtain ⟨DB⟩ := DualExistence.Construction.geometricCanonicalQuotientDual_nonempty D pol k s n hn f hker hlag hc
  have hl := StandardWeilIsotropy.Construction.canonicalKernel_standardWeil_selfAnnihilating (D.pullback s) (pol.pullback s) n hn f.hom hker hlag
  obtain ⟨p, hp, _hu⟩ := Picard.PoincareBundle.Canonical.WeilPolarizationDescent.existsUnique_polarization
    (D.pullback s) DB (pol.pullback s) f n hn hc hker hl
  rw [SharedDualMapComparison.Construction.e45SharedDualMap_eq_native] at hp
  exact ⟨DB, p, hp⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PolarizationExistence.Construction
