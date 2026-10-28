import OAI.AlgebraicGeometry.PELModuli.CMPoints.RankSpecialization
import OAI.AlgebraicGeometry.GroupSchemes.EtaleCyclic
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Etale Rank -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.EtaleRank

noncomputable section

/-! For an actual finite etale group over an algebraically closed
field, the coordinate dimension is the number of its rational points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def affineFieldBaseIso (k : Type) [Field k] :
    GroupSchemes.FiniteEtale.affine k (CommAlgCat.of k k) ≅ Over.mk (𝟙 (Spec (.of k))) :=
  Over.isoMk (Iso.refl _) (by
    change (𝟙 (Spec (.of k))) ≫ (𝟙 (Spec (.of k))) =
      Spec.map (CommRingCat.ofHom (algebraMap k k))
    simp)

theorem finite_etale_group_points_rank {k : Type} [Field k] [IsAlgClosed k]
    (G : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k) [Etale G.scheme.hom] :
    Module.finrank k G.algebra = Nat.card G.rationalPoints := by
  have h : (algebraMap k G.algebra).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)
      (φ := CommRingCat.ofHom (algebraMap k G.algebra))).mp
      (inferInstance : Etale G.scheme.hom)
  let : Algebra.Etale k G.algebra := RingHom.etale_algebraMap.mp h
  exact G.rationalPoints_card.symm

theorem finite_etale_group_basePoints_rank {k : Type} [Field k] [IsAlgClosed k]
    (G : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k) [Etale G.scheme.hom] :
    Module.finrank k G.algebra = Nat.card (Over.mk (𝟙 (Spec (.of k))) ⟶ G.scheme) :=
  (finite_etale_group_points_rank G).trans
    (Nat.card_congr (Iso.homCongr (affineFieldBaseIso k) (Iso.refl G.scheme)))

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.EtaleRank
