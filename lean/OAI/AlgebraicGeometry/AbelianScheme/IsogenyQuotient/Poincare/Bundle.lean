import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PolarizationAdapter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SharedDualMapComparison

/-! # Bundle -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.Bundle.Construction

noncomputable section

/-! Complete field-level PoincareBundle prerequisite: the original canonical
polarization pairing, full scheme-valued kernel and annihilator, unchanged
polarization type, and uniqueness of the actual polarization homomorphism.
All fields are allowed, including characteristic q. Relative families are
not part of the PoincareBundle statement schema. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

def PoincareBundleInput : Prop :=
  ∀ {k : Type} [Field k] {g : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
    (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) {δ : Fin g → ℕ}
    (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DA δ) (q h : ℕ) (hq : q.Prime)
    (_hdegree : Nat.Coprime q ((∏ i, δ i) ^ 2)) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
    (_hkernel : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme),
      x ≫ f.hom = 1 → x ^ (q ^ h) = 1)
    (_hlagrangian :
      let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme (q ^ h)) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.hom)
      (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing A DA pol (q ^ h) (pow_pos hq.pos h)).relativeAnnihilator F = F),
    ∃ p : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB δ,
      (f.hom ≫ p.isogeny.hom ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB =
        pol.isogeny.hom ^ (q ^ h)) ∧
      ∀ (ε : Fin g → ℕ) (r : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DB ε),
        f.hom ≫ r.isogeny.hom ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB =
          pol.isogeny.hom ^ (q ^ h) → r.isogeny = p.isogeny

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.Bundle.Construction
