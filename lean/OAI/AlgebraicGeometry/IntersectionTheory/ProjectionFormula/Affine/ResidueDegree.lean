import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward
import Mathlib.RingTheory.RamificationInertia.Inertia

/-! # Residue Degree -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ResidueDegree

noncomputable section

/-! The inertia degree in the algebraic norm formula equals the native
scheme residue degree in ProjectionFormula's cycle pushforward. The proof compares the
canonical residue-field morphisms through their maps from spectra. -/

set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem residueFieldIso_hom_fromSpec (R : CommRingCat.{u}) (x : PrimeSpectrum R) :
    Spec.map (Scheme.Spec.residueFieldIso R x).hom ≫ (Spec R).fromSpecResidueField x =
      Spec.map (CommRingCat.ofHom (algebraMap R x.asIdeal.ResidueField)) := by
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
    ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem residueField_square (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) :
    letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
    let f := Spec.map (CommRingCat.ofHom (algebraMap R S))
    f.residueFieldMap q ≫ (Scheme.Spec.residueFieldIso (.of S) q).hom =
      (Scheme.Spec.residueFieldIso (.of R) (f q)).hom ≫
        CommRingCat.ofHom (algebraMap (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) := by
  let := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
  let f := Spec.map (CommRingCat.ofHom (algebraMap R S))
  change f.residueFieldMap q ≫ _ = _
  rw [← Spec.map_inj]
  apply (cancel_mono ((Spec (.of R)).fromSpecResidueField (f q))).mp
  simp only [Spec.map_comp, Category.assoc,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [residueFieldIso_hom_fromSpec, ← Category.assoc, residueFieldIso_hom_fromSpec,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  exact (IsScalarTower.algebraMap_apply R S q.asIdeal.ResidueField r).symm.trans
    (IsScalarTower.algebraMap_apply R (q.asIdeal.under R).ResidueField
      q.asIdeal.ResidueField r)

/-- On affine schemes the two native degree definitions are identical. -/
theorem residueDegree_eq_inertiaDeg (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).residueDegree q = q.asIdeal.inertiaDeg R := by
  let := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
  let := ((Spec.map (CommRingCat.ofHom (algebraMap R S))).residueFieldMap q).hom.toAlgebra
  let : Algebra ((Spec.map (CommRingCat.ofHom (algebraMap R S))) q).asIdeal.ResidueField
      q.asIdeal.ResidueField :=
    inferInstanceAs (Algebra (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField)
  rw [Ideal.inertiaDeg_def]
  apply Algebra.finrank_eq_of_equiv_equiv
    (Scheme.Spec.residueFieldIso (.of R)
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))) q)).commRingCatIsoToRingEquiv
    (Scheme.Spec.residueFieldIso (.of S) q).commRingCatIsoToRingEquiv
  exact congrArg CommRingCat.Hom.hom (residueField_square R S q).symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ResidueDegree
