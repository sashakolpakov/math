import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.SliceSheaves
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SliceAcyclicity

/-! # Slice Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SliceCohomology

noncomputable section

/-!
# IntegralComparison: actual bounded slice cohomology and affine vanishing

The slice equivalence preserves both original coefficients. Hence its
map on Ext identifies bounded slice cohomology with the already proved
original slice calculation, in every degree.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

section General

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (U : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

instance hasExt : HasExt.{u + 2} (BoundedCrystalline.SliceSheaves.SliceSheaf f n U) :=
  HasExt.standard _

abbrev Cohomology (i : ℕ) := Abelian.Ext.{u + 2}
  (BoundedCrystalline.SliceSheaves.constantUnit f n U)
  (BoundedCrystalline.SliceSheaves.structureSheaf f n U) i

def cohomologyEquiv (i : ℕ) : Crystalline.SliceStructure.Cohomology U.obj i ≃+ Cohomology f n U i :=
  (AddEquiv.ofBijective ((BoundedCrystalline.SliceSheaves.equivalence f n U).functor.mapExtAddHom
    (CrystallinePrincipal.Constant.Comparison.constantUnit U.obj) (Crystalline.SliceStructure.structureSheaf U.obj) i)
    ((BoundedCrystalline.SliceSheaves.equivalence f n U).functor.mapExt_bijective_of_preservesInjectiveObjects
      (CrystallinePrincipal.Constant.Comparison.constantUnit U.obj) (Crystalline.SliceStructure.structureSheaf U.obj) i)).trans
    (Etale.Frobenius.extIsoCongr (Crystalline.ExactRestriction.Coeff (B := B))
      (BoundedCrystalline.SliceSheaves.constantUnitIso f n U)
      (BoundedCrystalline.SliceSheaves.structureSheafIso f n U) i).toAddEquiv

end General

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k))) (n : ℕ)
  (U : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

theorem positive_cohomology_zero (i : ℕ) : Subsingleton (Cohomology f n U (i + 1)) := by
  have := Crystalline.SliceAcyclicity.positive_cohomology_zero p k U.obj i
  exact (cohomologyEquiv f n U (i + 1)).symm.toEquiv.subsingleton

def degreeZeroEquiv : Cohomology f n U 0 ≃+ ULift.{u + 1} U.obj.ring :=
  (cohomologyEquiv f n U 0).symm.trans (Crystalline.SliceAcyclicity.degreeZeroEquiv p k U.obj)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SliceCohomology
