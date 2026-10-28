import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldPolarization
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.FieldWeilIsotropy
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Scheme

/-! # Field Intrinsic Poincare Bundle -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldIntrinsicPoincareBundle.ModeledIntrinsic

noncomputable section

/-! Apply the accepted PoincareBundle theorem to the actual original-field kernel.
Its positive polarization is identified with the modeled polarization by
the uniqueness conclusion of that same theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.FieldWeilIsotropy.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CanonicalAlternation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedPairingBaseChange OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldPolarization

variable {k L : Type} [Field k] [Field L] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (a : Spec (.of L) ⟶ Spec (.of k))
  (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.abelian.scheme (Over.mk a)) (R : F.Model)
  (q h : ℕ) (hq : q.Prime)
  (Q : ModeledAbelian.Lifts.ModeledAbelianQuotient A.abelian (Over.mk a) F R (q ^ h))
  (hdegree : q.Coprime ((∏ i, δ i) ^ 2))
  (hF :
    let b := AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A.abelian A.dual A.polarization
      (q ^ h) (pow_pos hq.pos h)
    let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme (q ^ h)) F
    b.relativeAnnihilator H = H)

include hF in
theorem modeledFieldKernel_nativeIsotropy :
    let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback
      (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion (A.abelian.pullback a).scheme (q ^ h))
      (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel Q.isogeny.hom)
    (AbelianScheme.IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.abelian.pullback a) (A.dual.pullback a)
      (A.polarization.pullback a) (q ^ h) (pow_pos hq.pos h)).relativeAnnihilator H = H := by
  have hk := AbelianScheme.IsogenyQuotient.Intrinsic.Isotropy.Construction.nativeQuotient_kernel_self_annihilating A.abelian (Over.mk a) F R
    Q.isogeny Q.kernel (q ^ h)
    (AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A.abelian A.dual A.polarization
      (q ^ h) (pow_pos hq.pos h)) hF
  let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback
    (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion (A.abelian.pullback a).scheme (q ^ h))
    (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel Q.isogeny.hom)
  have hb := (ReducedPairingBaseChange.reducedCanonicalPairing_baseChange A.abelian A.dual A.polarization a
    (q ^ h) (pow_pos hq.pos h)).symm.trans
      (NeighborCounting.Field.CanonicalAlternation.reducedPairing_eq_field (A.abelian.pullback a) (A.dual.pullback a)
        (A.polarization.pullback a) (q ^ h) (pow_pos hq.pos h))
  exact (congrArg (fun e : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
    (A := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme (A.abelian.pullback a).scheme (q ^ h))
    (B := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme (A.abelian.pullback a).scheme (q ^ h))
    (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of L))).X) =>
      e.relativeAnnihilator H) hb).symm.trans hk

def modeledNativePoincareBundleExistenceIdentity :=
  PLift.up (Picard.PoincareBundle.Scheme.proved L g (A.abelian.pullback a) Q.target
    (A.dual.pullback a) (ModeledFieldPolarization.modeledFieldDual A a F R (q ^ h) (pow_pos hq.pos h) Q) δ
    (A.polarization.pullback a) Q.isogeny q h hq hdegree Q.kernel_bound
    (AbelianScheme.IsogenyQuotient.Reference.FieldWeilIsotropy.Construction.canonicalKernel_originalFieldWeil_selfAnnihilating (A.dual.pullback a)
      (A.polarization.pullback a) (q ^ h) (pow_pos hq.pos h) Q.isogeny Q.kernel_bound
      (modeledFieldKernel_nativeIsotropy A a F R q h hq Q hF)))

include hdegree hF in
theorem modeledNativePoincareBundle_exists :
    type_of% (modeledNativePoincareBundleExistenceIdentity A a F R q h hq Q hdegree hF).down :=
  (modeledNativePoincareBundleExistenceIdentity A a F R q h hq Q hdegree hF).down

def modeledNativePoincareBundlePolarization :=
  (modeledNativePoincareBundle_exists A a F R q h hq Q hdegree hF).choose

attribute [local irreducible] ModeledFieldPolarization.modeledFieldDual ModeledFieldPolarization.modeledFieldPolarization

theorem modeledFieldPolarization_eq_nativePoincareBundle :
    (ModeledFieldPolarization.modeledFieldPolarization A a F R (q ^ h) (pow_pos hq.pos h) Q
      (hdegree.pow_left h) hF).isogeny =
        (modeledNativePoincareBundlePolarization A a F R q h hq Q hdegree hF).isogeny := by
  have hp := (AbelianScheme.FrobeniusKernel.BundleIntrinsicDualMap.Construction.IntrinsicPicardPullback.e45Pullback_eq Q.isogeny.hom (A.dual.pullback a)
    (ModeledFieldPolarization.modeledFieldDual A a F R (q ^ h) (pow_pos hq.pos h) Q)
    (ModeledFieldPolarization.modeledFieldPolarization A a F R (q ^ h) (pow_pos hq.pos h) Q
      (hdegree.pow_left h) hF).isogeny.hom).trans
        (ModeledFieldPolarization.modeledFieldPolarization_nativePullback A a F R (q ^ h) (pow_pos hq.pos h) Q
          (hdegree.pow_left h) hF)
  exact (modeledNativePoincareBundle_exists A a F R q h hq Q hdegree hF).choose_spec.2 δ
    (ModeledFieldPolarization.modeledFieldPolarization A a F R (q ^ h) (pow_pos hq.pos h) Q
      (hdegree.pow_left h) hF) hp

theorem modeledFieldPolarization_acceptedPullback :
    AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom Q.isogeny.hom (A.dual.pullback a)
      (ModeledFieldPolarization.modeledFieldDual A a F R (q ^ h) (pow_pos hq.pos h) Q)
      (ModeledFieldPolarization.modeledFieldPolarization A a F R (q ^ h) (pow_pos hq.pos h) Q
        (hdegree.pow_left h) hF) =
      (A.polarization.pullback a).isogeny.hom ^ (q ^ h) := by
  apply (AbelianScheme.FrobeniusKernel.BundleIntrinsicDualMap.Construction.IntrinsicPicardPullback.e45Pullback_eq Q.isogeny.hom (A.dual.pullback a)
    (ModeledFieldPolarization.modeledFieldDual A a F R (q ^ h) (pow_pos hq.pos h) Q)
    (ModeledFieldPolarization.modeledFieldPolarization A a F R (q ^ h) (pow_pos hq.pos h) Q
      (hdegree.pow_left h) hF).isogeny.hom).symm.trans
  rw [modeledFieldPolarization_eq_nativePoincareBundle A a F R q h hq Q hdegree hF]
  exact (modeledNativePoincareBundle_exists A a F R q h hq Q hdegree hF).choose_spec.1

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldIntrinsicPoincareBundle.ModeledIntrinsic
