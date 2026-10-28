import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicTorsionFunctor
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalTorsionCartierIso

/-! # Canonical Dual Torsion Functor -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalDualTorsionFunctor.Construction

noncomputable section

/-! Identify the actual Picard group on the specified dual with its
original HilbertConstruction torsion functor, using the proved group-law comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))) (n : ℕ)

def canonicalDualTorsionYonedaIso :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual)
    letI : IsCommMonObj (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).abelian :=
      Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual)
    yonedaGrp.obj (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup
      (Grp.mk (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).abelian) n) ≅ A.dual.abelian.torsionFunctor n := by
  let D := Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual
  let i := IntrinsicTorsionFunctor.Construction.nativeTorsionGroupStructureIso D.abelian (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D) D.group
    (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D) D.commutative (Picard.Homomorphisms.UnbundledDualGroupComparison.Construction.UnbundledPicard.dualPicardGroup_eq_given D) n
  exact yonedaGrp.mapIso i ≪≫ IntrinsicTorsionFunctor.Construction.nativeTorsionYonedaIso A.dual.abelian n

theorem canonicalDualTorsionYonedaIso_value (T : Over (Spec (.of k))) :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual)
    letI : IsCommMonObj (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).abelian :=
      Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual)
    ∀ x : T ⟶ (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup
        (Grp.mk (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).abelian) n).X,
      ((canonicalDualTorsionYonedaIso A n).hom.app (.op T) x).val =
        x ≫ TorsionQuotient.SubgroupFunctor.torsionι (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual).abelian n := by
  let D := Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled A.dual
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  have : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
  intro x
  let i := IntrinsicTorsionFunctor.Construction.nativeTorsionGroupStructureIso D.abelian (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D) D.group
    (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D) D.commutative (Picard.Homomorphisms.UnbundledDualGroupComparison.Construction.UnbundledPicard.dualPicardGroup_eq_given D) n
  have hi := IntrinsicTorsionFunctor.Construction.nativeTorsionGroupStructureIso_inclusion D.abelian (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D) D.group
    (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D) D.commutative (Picard.Homomorphisms.UnbundledDualGroupComparison.Construction.UnbundledPicard.dualPicardGroup_eq_given D) n
  change ((IntrinsicTorsionFunctor.Construction.nativeTorsionYonedaIso A.dual.abelian n).hom.app (.op T) (x ≫ i.hom.hom.hom)).val = _
  exact (IntrinsicTorsionFunctor.Construction.nativeTorsionYonedaIso_value A.dual.abelian n T (x ≫ i.hom.hom.hom)).trans
    ((Category.assoc x i.hom.hom.hom (TorsionQuotient.SubgroupFunctor.torsionι A.dual.abelian.scheme n)).trans
      (congrArg (fun z => x ≫ z) hi))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalDualTorsionFunctor.Construction
