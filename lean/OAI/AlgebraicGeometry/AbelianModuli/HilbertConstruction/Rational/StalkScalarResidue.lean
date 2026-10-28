import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PointResidue
import Mathlib.RingTheory.Etale.Basic

/-! # Stalk Scalar Residue -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.StalkScalarResidue

noncomputable section

/-! At a rational point, the ground-field coefficient map to the actual residue field is the inverse of the geometric residue-field isomorphism. Its formal etaleness is derived with this actual scalar action. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
variable (p : X ⟶ Spec (.of K)) (s : Spec (.of K) ⟶ X) (hs : s ≫ p = 𝟙 _)

def rationalStalkResidueCoefficient : K →+* X.residueField (s (IsLocalRing.closedPoint K)) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop ≫ X.Γevaluation (s (IsLocalRing.closedPoint K))).hom

private theorem rationalPoint_top_germ_to_ground :
    X.presheaf.germ ⊤ (s (IsLocalRing.closedPoint K)) trivial ≫ Scheme.stalkClosedPointTo s =
      s.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom := by
  have h := Scheme.germ_stalkClosedPointTo s ⊤ trivial
  change X.presheaf.germ ⊤ (s (IsLocalRing.closedPoint K)) trivial ≫ Scheme.stalkClosedPointTo s =
    s.appTop ≫ ((Spec (.of K)).presheaf.map (𝟙 (op (⊤ : (Spec (.of K)).Opens))) ≫
      (Scheme.ΓSpecIso (.of K)).hom) at h
  rw [(Spec (.of K)).presheaf.map_id, Category.id_comp] at h
  exact h

theorem rationalStalkResidueCoefficient_comp_residueIso :
    CommRingCat.ofHom (rationalStalkResidueCoefficient p s) ≫ (PointResidue.rationalPointResidueIso p s hs).hom =
      𝟙 (CommRingCat.of K) := by
  let x := s (IsLocalRing.closedPoint K)
  have hg : X.presheaf.germ ⊤ x trivial ≫ Scheme.stalkClosedPointTo s =
      s.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom := rationalPoint_top_germ_to_ground s
  change ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop ≫
      (X.presheaf.germ ⊤ x trivial ≫ X.residue x)) ≫
        X.descResidueField (Scheme.stalkClosedPointTo s) = 𝟙 (CommRingCat.of K)
  rw [Category.assoc, Category.assoc, Category.assoc, Scheme.residue_descResidueField,
    hg, ← Category.assoc p.appTop s.appTop]
  rw [← Scheme.Hom.comp_appTop, hs, Scheme.Hom.id_appTop, Category.id_comp,
    (Scheme.ΓSpecIso (.of K)).inv_hom_id]

include hs in
theorem rationalStalkResidueCoefficient_bijective :
    Function.Bijective (rationalStalkResidueCoefficient p s) := by
  let e := PointResidue.rationalPointResidueIso p s hs
  refine ⟨(rationalStalkResidueCoefficient p s).injective, ?_⟩
  intro y
  refine ⟨e.hom y, ?_⟩
  apply e.commRingCatIsoToRingEquiv.injective
  exact ConcreteCategory.congr_hom (rationalStalkResidueCoefficient_comp_residueIso p s hs) (e.hom y)

include hs in
theorem rationalStalkResidue_formallyEtale :
    let : Algebra K (X.residueField (s (IsLocalRing.closedPoint K))) :=
      (rationalStalkResidueCoefficient p s).toAlgebra;
    Algebra.FormallyEtale K (X.residueField (s (IsLocalRing.closedPoint K))) := by
  let : Algebra K (X.residueField (s (IsLocalRing.closedPoint K))) :=
    (rationalStalkResidueCoefficient p s).toAlgebra
  let e : K ≃ₐ[K] X.residueField (s (IsLocalRing.closedPoint K)) :=
    AlgEquiv.ofBijective (Algebra.ofId K _) (rationalStalkResidueCoefficient_bijective p s hs)
  exact Algebra.FormallyEtale.of_equiv e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.StalkScalarResidue
