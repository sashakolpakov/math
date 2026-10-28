import OAI.AlgebraicGeometry.FormalGeometry.Completion.EtaleCoordinateCharacters
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.PointAlgebraHom
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteHopfPresentation
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Etale Group Point Count -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.EtaleGroupPointCount

noncomputable section

/-! The number of geometric points of an actual finite etale
commutative group is its structural degree. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory

namespace Construction

universe u

theorem etale_card_algHom_eq_finrank (K R : Type u)
    [Field K] [IsAlgClosed K] [CommRing R] [Algebra K R]
    [Module.Finite K R] [Algebra.Etale K R] :
    Nat.card (R →ₐ[K] K) = Module.finrank K R := by
  have : Finite (R →ₐ[K] K) := (linearIndependent_algHom_toLinearMap K R K).finite
  let := Fintype.ofFinite (R →ₐ[K] K)
  apply Nat.le_antisymm
  · simpa only [Nat.card_eq_fintype_card, Subspace.dual_finrank_eq] using
      (linearIndependent_algHom_toLinearMap K R K).fintype_card_le_finrank
  · exact EtaleCoordinateCharacters.Construction.etale_finrank_le_card_algHom K R

theorem finiteEtaleGroup_card_points_eq_finrank {K : Type u} [Field K] [IsAlgClosed K]
    (G : Grp (Over (Spec (.of K)))) [IsCommMonObj G.X]
    [IsFinite G.X.hom] [Etale G.X.hom] (x : Spec (.of K)) :
    Nat.card (𝟙_ (Over (Spec (.of K))) ⟶ G.X) = G.X.hom.finrank x := by
  obtain ⟨R, hR, _, ⟨e⟩⟩ := Picard.Homomorphisms.FiniteHopfPresentation.Construction.finite_commutative_hopfPresentation K G
  have : Module.Finite K R := hR
  let i : ((hopfSpec (.of K)).obj (.op R)).X ≅ G.X := (Grp.forget _).mapIso e
  have : IsIso i.hom.left := inferInstanceAs (IsIso ((Over.forget _).map i.hom))
  have het : Etale (((hopfSpec (.of K)).obj (.op R)).X).hom := by
    rw [← i.hom.w]
    infer_instance
  have : Algebra.Etale K R := RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp het)
  have hp : Nat.card (R →ₐ[K] K) = Nat.card (𝟙_ (Over (Spec (.of K))) ⟶ G.X) :=
    Nat.card_congr ((Affine.PointAlgebraHom.Construction.affineFieldPointsEquivAlgHom K R).symm.trans (Iso.homCongr (Iso.refl _) i))
  calc
    Nat.card (𝟙_ (Over (Spec (.of K))) ⟶ G.X) = Module.finrank K R :=
      hp.symm.trans (etale_card_algHom_eq_finrank K R)
    _ = (((hopfSpec (.of K)).obj (.op R)).X).hom.finrank x := by
      change _ = (Spec.map (CommRingCat.ofHom (algebraMap K R))).finrank x
      rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
      rfl
    _ = G.X.hom.finrank x := by
      rw [← i.hom.w, Scheme.Hom.finrank_comp_left_of_isIso]

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.EtaleGroupPointCount
