import OAI.RepresentationTheory.Theta.Geometric.Cubical.FamilySeparation
import OAI.RepresentationTheory.Theta.Geometric.AutomorphicFamilyProducts
import OAI.RepresentationTheory.Theta.Geometric.TriplePeriodMaps
import OAI.RepresentationTheory.Theta.Geometric.AutomorphicFamilies

/-! # Triple Embedding -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The original theta embedding supplies an embedding and tangent
detection for the positive cubical family on the triple period torus. -/

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.tripleCube : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (J.leftCubeFactor Φ.tripleFirst Φ.tripleSecond Φ.tripleThird
    Φ.tripleFirst_mem Φ.tripleSecond_mem Φ.tripleThird_mem) :=
  F.leftCube Φ.tripleFirst Φ.tripleSecond Φ.tripleThird
    Φ.tripleFirst_mem Φ.tripleSecond_mem Φ.tripleThird_mem

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.separates_of_projective_injective (hF : Function.Injective F.projectiveMap)
    (p q : Φ.space) (hpq : p - q ∉ Φ.periodIntegerLattice) : F.Separates p q := by
  by_contra h
  exact hpq (QuotientAddGroup.eq_iff_sub_mem.mp (hF ((F.projectiveMap_eq_of_not_separates p q).mpr h)))

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.tripleCube_separates (hF : Function.Injective F.projectiveMap)
    (p q : Φ.triple.space) (hpq : p - q ∉ Φ.triple.periodIntegerLattice) :
    F.tripleCube.Separates p q := by
  apply AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.leftCube_separates_coordinates
  rcases Φ.triple_coordinate_outside p q hpq with h1 | h2 | h3
  · exact Or.inl (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap_separates Φ.tripleFirst Φ.tripleFirst_mem F p q
      (F.separates_of_projective_injective hF _ _ h1))
  · exact Or.inr (Or.inl (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap_separates Φ.tripleSecond Φ.tripleSecond_mem F p q
      (F.separates_of_projective_injective hF _ _ h2)))
  · exact Or.inr (Or.inr (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap_separates Φ.tripleThird Φ.tripleThird_mem F p q
      (F.separates_of_projective_injective hF _ _ h3)))

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.tripleCube_injective (hF : Function.Injective F.projectiveMap) :
    Function.Injective F.tripleCube.projectiveMap := by
  intro p q hpq
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective p
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective q
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  by_contra hvw
  exact (F.tripleCube.projectiveMap_eq_of_not_separates v w).mp hpq
    (F.tripleCube_separates hF v w hvw)

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.tripleCube_detects (hF : ∀ p v : Φ.space, v ≠ 0 → F.Detects p v)
    (p v : Φ.triple.space) (hv : v ≠ 0) : F.tripleCube.Detects p v := by
  apply AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.leftCube_detects_coordinates
  rcases Φ.triple_coordinate_nonzero v hv with h1 | h2 | h3
  · exact Or.inl (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap_detects Φ.tripleFirst Φ.tripleFirst_mem F p v (hF _ _ h1))
  · exact Or.inr (Or.inl (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap_detects Φ.tripleSecond Φ.tripleSecond_mem F p v (hF _ _ h2)))
  · exact Or.inr (Or.inr (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap_detects Φ.tripleThird Φ.tripleThird_mem F p v (hF _ _ h3)))

end

end OAI.RepresentationTheory.Theta.Geometric
