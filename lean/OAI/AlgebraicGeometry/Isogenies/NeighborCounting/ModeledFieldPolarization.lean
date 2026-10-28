import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledQuotientKernelBound
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualExistence
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CanonicalAlternation
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedPairingBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.Isotropy
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.CanonicalIsotropyBaseChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GeneralFieldPolarizationDescent
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BundleIntrinsicDualMap

/-! # Modeled Field Polarization -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldPolarization

noncomputable section

/-! Construct the dual and positive polarization of the actual modeled
field quotient. The exact relative kernel's isotropy is transported to
the quotient's scheme kernel before applying polarization descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CanonicalAlternation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ReducedPairingBaseChange

variable {k L : Type} [Field k] [Field L] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (a : Spec (.of L) ⟶ Spec (.of k))
  (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.abelian.scheme (Over.mk a)) (R : F.Model)
  (n : ℕ) (hn : 0 < n) (Q : ModeledAbelian.Lifts.ModeledAbelianQuotient A.abelian (Over.mk a) F R n)

def modeledFieldDual : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData Q.target :=
  FieldQuotient.DualExistence.isogenousQuotientDualData (A.dual.pullback a)
    (A.polarization.pullback a).isogeny Q.isogeny n hn Q.kernel_bound

variable (hdegree : n.Coprime ((∏ i, δ i) ^ 2))
  (hF :
    let b := AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A.abelian A.dual A.polarization n hn
    let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme n) F
    b.relativeAnnihilator H = H)

include hF in
theorem modeledFieldKernel_geometricIsotropy :
    Picard.PoincareBundle.Geometric.WeilIsotropy.SelfAnnihilating (A.dual.pullback a)
      (A.polarization.pullback a) Q.isogeny n hn Q.kernel_bound := by
  apply AbelianScheme.IsogenyQuotient.Field.CanonicalIsotropyBaseChange.Construction.canonicalKernel_geometric_standardWeil_selfAnnihilating (A.dual.pullback a)
    (A.polarization.pullback a) Q.isogeny n hn Q.kernel_bound
  have h := AbelianScheme.IsogenyQuotient.Intrinsic.Isotropy.Construction.nativeQuotient_kernel_self_annihilating A.abelian (Over.mk a) F R
    Q.isogeny Q.kernel n (AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A.abelian A.dual A.polarization n hn) hF
  let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback
    (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion (A.abelian.pullback a).scheme n)
    (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel Q.isogeny.hom)
  have hb := (ReducedPairingBaseChange.reducedCanonicalPairing_baseChange A.abelian A.dual A.polarization a n hn).symm.trans
    (NeighborCounting.Field.CanonicalAlternation.reducedPairing_eq_field (A.abelian.pullback a) (A.dual.pullback a)
      (A.polarization.pullback a) n hn)
  exact (congrArg (fun e : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
    (A := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme (A.abelian.pullback a).scheme n)
    (B := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme (A.abelian.pullback a).scheme n)
    (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of L))).X) =>
      e.relativeAnnihilator H) hb).symm.trans h

def modeledFieldPolarization : AbelianModuli.HilbertConstruction.PolarizationData.Polarization (modeledFieldDual A a F R n hn Q) δ :=
  (Picard.PoincareBundle.GeneralFieldPolarizationDescent.existsUnique_polarization (A.dual.pullback a)
    (modeledFieldDual A a F R n hn Q) (A.polarization.pullback a) Q.isogeny n hn hdegree
    Q.kernel_bound (modeledFieldKernel_geometricIsotropy A a F R n hn Q hF)).choose

theorem modeledFieldPolarization_nativePullback :
    AbelianScheme.FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom Q.isogeny.hom (A.dual.pullback a)
      (modeledFieldDual A a F R n hn Q) (modeledFieldPolarization A a F R n hn Q hdegree hF) =
        (A.polarization.pullback a).isogeny.hom ^ n :=
  (AbelianScheme.FrobeniusKernel.BundleIntrinsicDualMap.Construction.IntrinsicPicardPullback.e45Pullback_eq Q.isogeny.hom (A.dual.pullback a)
    (modeledFieldDual A a F R n hn Q)
    (modeledFieldPolarization A a F R n hn Q hdegree hF).isogeny.hom).symm.trans
      (Picard.PoincareBundle.GeneralFieldPolarizationDescent.existsUnique_polarization (A.dual.pullback a)
        (modeledFieldDual A a F R n hn Q) (A.polarization.pullback a) Q.isogeny n hn hdegree
        Q.kernel_bound (modeledFieldKernel_geometricIsotropy A a F R n hn Q hF)).choose_spec.1

def modeledFieldPolarized (hlevel : n.Coprime N) :
    AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of L)) where
  abelian := Q.target
  dual := modeledFieldDual A a F R n hn Q
  polarization := modeledFieldPolarization A a F R n hn Q hdegree hF
  level := Q.level N hlevel (A.pullback a).level

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldPolarization
