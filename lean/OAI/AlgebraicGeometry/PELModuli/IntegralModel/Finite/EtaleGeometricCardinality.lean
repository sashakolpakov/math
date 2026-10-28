import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.EtaleFiberDegree
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Etale Geometric Cardinality -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleGeometricCardinality

noncomputable section

/-! The number of actual rational points of a finite etale scheme over an
algebraically closed field equals its scheme-theoretic rank. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints

def affineFieldBaseIso (K : Type) [Field K] :
    Foundations.Scheme.AffineComplexPoints.affineSchemeOver K K ≅ Over.mk (𝟙 (Spec (.of K))) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 (Spec (.of K)) ≫ 𝟙 (Spec (.of K)) = Spec.map (CommRingCat.ofHom (algebraMap K K))
    simp)

theorem finiteEtale_geometric_point_card {K : Type} [Field K] [IsAlgClosed K]
    (H : Over (Spec (.of K))) [IsFinite H.hom] [Etale H.hom] (z : Spec (.of K)) :
    Nat.card (Over.mk (𝟙 (Spec (.of K))) ⟶ H) = H.hom.finrank z := by
  have : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨B, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of K) (G := H)).mpr
    (inferInstanceAs (IsAffine H.left))
  let A := B.unop
  let Q := Foundations.Scheme.AffineComplexPoints.affineSchemeOver K A
  change Q ≅ H at e
  have : IsFinite Q.hom := by
    rw [← e.hom.w]
    infer_instance
  have : Etale Q.hom := by
    rw [← e.hom.w]
    infer_instance
  have hfin : (algebraMap K A).Finite := (IsFinite.SpecMap_iff
    (CommRingCat.ofHom (algebraMap K A))).mp (inferInstanceAs (IsFinite Q.hom))
  have : Module.Finite K A := (RingHom.finite_algebraMap).mp hfin
  have het : (algebraMap K A).Etale := (HasRingHomProperty.Spec_iff (P := @Etale)
    (φ := CommRingCat.ofHom (algebraMap K A))).mp (inferInstanceAs (Etale Q.hom))
  have : Algebra.Etale K A := (RingHom.etale_algebraMap).mp het
  let ep := (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv K A K).trans ((affineFieldBaseIso K).homCongr e)
  have hc : Nat.card (Over.mk (𝟙 (Spec (.of K))) ⟶ H) = Module.finrank K A :=
    (Nat.card_congr ep).symm.trans
      (CycleClass.Thom.ProperImage.EtaleFiberDegree.Constructions.Construction.card_characters_eq_finrank_of_etale K A)
  have hr : Q.hom.finrank z = H.hom.finrank z := by
    rw [← e.hom.w, Scheme.Hom.finrank_comp_left_of_isIso]
  rw [hc, ← hr]
  change Module.finrank K A = (Spec.map (CommRingCat.ofHom (algebraMap K A))).finrank z
  rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleGeometricCardinality
