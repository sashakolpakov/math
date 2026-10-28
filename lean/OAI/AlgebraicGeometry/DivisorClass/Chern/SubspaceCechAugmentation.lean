import OAI.AlgebraicGeometry.DivisorClass.Chern.SubspaceCechD
import OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CechSequence

/-! # Subspace Cech Augmentation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SubspaceCechAugmentation

noncomputable section

/-!
# ChernClass: global cochains on the removed subspace and its Cech complex

The usual singular augmentation on the induced open cover transports through
the actual intersection homeomorphisms. Its cohomology isomorphism therefore
comes from the genuine global singular cochains of the removed subspace.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech

variable {I : Type} (X : TopCat.{0}) (A : Set X) (U : I → Opens X)

/-- The total transport is the actual intersection pullback in every homogeneous summand. -/
theorem subspaceCechTotalIso_inclusion (p q n : ℕ) (hpq : p + q = n)
    (c : Rational.Cech.RationalCech.CechCochain (SubspaceCechD.RationalCech.subspaceSingularDegreePresheaf X A q) U p) :
    (SubspaceCechD.RationalCech.subspaceCechTotalIso X A U).hom.f n
      (Rational.Cech.RationalCech.cechTotalInclusion U (SubspaceCechD.RationalCech.subspaceSingularPresheafComplex X A) p q n hpq c) =
    Rational.Cech.RationalCech.cechTotalInclusion (SubspaceCechD.RationalCech.inducedSubspaceCover X A U)
      (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of A)) p q n hpq
        ((SubspaceCechD.RationalCech.subspaceCechColumnMap X A U p).f q c) :=
  AlgebraicTopology.DeRham.Comparison.DoubleComplexMapComponents.DoubleComplex.total_map_iota (SubspaceCechD.RationalCech.subspaceCechDoubleIso X A U).hom p q n hpq c

/-- The genuine singular augmentation on the subspace, expressed in the actual coefficient model. -/
def subspaceCechAugmentation :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of A) ⟶ Relative.CechSequence.RationalCech.subspaceCechTotal X A U :=
  Rational.CechComparison.RationalCech.globalSingularCechAugmentation (TopCat.of A) (SubspaceCechD.RationalCech.inducedSubspaceCover X A U) (ModuleCat.of ℚ ℚ) ≫
    (SubspaceCechD.RationalCech.subspaceCechTotalIso X A U).inv

theorem subspaceCechAugmentation_transport :
    subspaceCechAugmentation X A U ≫ (SubspaceCechD.RationalCech.subspaceCechTotalIso X A U).hom =
      Rational.CechComparison.RationalCech.globalSingularCechAugmentation (TopCat.of A) (SubspaceCechD.RationalCech.inducedSubspaceCover X A U) (ModuleCat.of ℚ ℚ) := by
  rw [subspaceCechAugmentation, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- This actual augmentation is a quasi-isomorphism for a genuine ambient open cover. -/
theorem subspaceCechAugmentation_quasiIso (hU : ∀ x : X, ∃ i, x ∈ U i) :
    QuasiIso (subspaceCechAugmentation X A U) := by
  have := Rational.CechComparison.RationalCech.rationalGlobalSingularCechAugmentation_quasiIso (TopCat.of A)
    (SubspaceCechD.RationalCech.inducedSubspaceCover X A U) (SubspaceCechD.RationalCech.inducedSubspaceCover_covers X A U hU)
  unfold subspaceCechAugmentation
  infer_instance

/-- The cohomology identification is induced by this actual global augmentation. -/
def subspaceCechCohomologyIso (hU : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of A) n ≅ (Relative.CechSequence.RationalCech.subspaceCechTotal X A U).homology n := by
  have := subspaceCechAugmentation_quasiIso X A U hU
  exact isoOfQuasiIsoAt (subspaceCechAugmentation X A U) n

theorem subspaceCechCohomologyIso_hom (hU : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (subspaceCechCohomologyIso X A U hU n).hom =
      HomologicalComplex.homologyMap (subspaceCechAugmentation X A U) n := rfl

end RationalCech

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SubspaceCechAugmentation
