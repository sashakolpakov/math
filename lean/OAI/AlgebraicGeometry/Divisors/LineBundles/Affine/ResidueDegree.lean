import OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationResidue
import Mathlib.RingTheory.RamificationInertia.Inertia

/-! # Residue Degree -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ResidueDegree.BundleCycles

noncomputable section

/-!
# LineBundleCycles: algebraic branch degrees equal actual scheme residue degrees

The comparison follows the canonical maps from residue-field spectra.
It identifies the inertia degrees in the finite normalization's branch
formula with the scheme residue degrees used by actual point pushforward.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

private theorem specIsoCancellation {A B : CommRingCat.{u}} (e : A ≅ B) {Y : Scheme.{u}} (g : Spec B ⟶ Y) :
    Spec.map e.hom ≫ (Spec.map e.inv ≫ g) = g := by
  rw [← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem specResidueFieldIso_fromSpec (R : CommRingCat.{u}) (x : PrimeSpectrum R) :
    Spec.map (Scheme.Spec.residueFieldIso R x).hom ≫ (Spec R).fromSpecResidueField x =
      Spec.map (CommRingCat.ofHom (algebraMap R x.asIdeal.ResidueField)) := by
  exact (congrArg (fun j => Spec.map (Scheme.Spec.residueFieldIso R x).hom ≫ j)
    (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField R x).symm).trans
      (specIsoCancellation (Scheme.Spec.residueFieldIso R x) _)

theorem affineResidueField_square (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) :
    letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
    let f := Spec.map (CommRingCat.ofHom (algebraMap R S))
    f.residueFieldMap q ≫ (Scheme.Spec.residueFieldIso (.of S) q).hom =
      (Scheme.Spec.residueFieldIso (.of R) (f q)).hom ≫
        CommRingCat.ofHom (algebraMap (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) := by
  let := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
  let f := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let eS := Scheme.Spec.residueFieldIso (CommRingCat.of S) q
  let eR := Scheme.Spec.residueFieldIso (CommRingCat.of R) (f q)
  let aS := CommRingCat.ofHom (algebraMap S q.asIdeal.ResidueField)
  let aR := CommRingCat.ofHom (algebraMap R (q.asIdeal.under R).ResidueField)
  let b := CommRingCat.ofHom (algebraMap (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField)
  let jR := (Spec (CommRingCat.of R)).fromSpecResidueField (f q)
  let jS := (Spec (CommRingCat.of S)).fromSpecResidueField q
  have hb : CommRingCat.ofHom (algebraMap R S) ≫ aS = aR ≫ b := by
    ext r
    exact (IsScalarTower.algebraMap_apply R S q.asIdeal.ResidueField r).symm.trans
      (IsScalarTower.algebraMap_apply R (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField r)
  have hm : Spec.map aS ≫ f = Spec.map b ≫ Spec.map aR :=
    (Spec.map_comp (CommRingCat.ofHom (algebraMap R S)) aS).symm.trans
      ((congrArg Spec.map hb).trans (Spec.map_comp aR b))
  apply Spec.map_injective
  apply (cancel_mono jR).mp
  exact (congrArg (fun j => j ≫ jR) (Spec.map_comp (f.residueFieldMap q) eS.hom)).trans
    ((Category.assoc (Spec.map eS.hom) (Spec.map (f.residueFieldMap q)) jR).trans
    ((congrArg (fun j => Spec.map eS.hom ≫ j) (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f q)).trans
    ((Category.assoc (Spec.map eS.hom) jS f).symm.trans
    ((congrArg (fun j => j ≫ f) (specResidueFieldIso_fromSpec (CommRingCat.of S) q)).trans
    (hm.trans ((congrArg (fun j => Spec.map b ≫ j) (specResidueFieldIso_fromSpec (CommRingCat.of R) (f q)).symm).trans
    ((Category.assoc (Spec.map b) (Spec.map eR.hom) jR).symm.trans
      (congrArg (fun j => j ≫ jR) (Spec.map_comp eR.hom b).symm))))))))

theorem affineResidueDegree_eq_inertiaDeg (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).residueDegree q = q.asIdeal.inertiaDeg R := by
  let := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
  let := ((Spec.map (CommRingCat.ofHom (algebraMap R S))).residueFieldMap q).hom.toAlgebra
  let eR : (Spec (CommRingCat.of R)).residueField ((Spec.map (CommRingCat.ofHom (algebraMap R S))) q) ≃+*
      (q.asIdeal.under R).ResidueField :=
    (Scheme.Spec.residueFieldIso (.of R) ((Spec.map (CommRingCat.ofHom (algebraMap R S))) q)).commRingCatIsoToRingEquiv
  let eS : (Spec (CommRingCat.of S)).residueField q ≃+* q.asIdeal.ResidueField :=
    (Scheme.Spec.residueFieldIso (.of S) q).commRingCatIsoToRingEquiv
  rw [Ideal.inertiaDeg_def]
  exact Algebra.finrank_eq_of_equiv_equiv eR eS
    (congrArg CommRingCat.Hom.hom (affineResidueField_square R S q).symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ResidueDegree.BundleCycles
