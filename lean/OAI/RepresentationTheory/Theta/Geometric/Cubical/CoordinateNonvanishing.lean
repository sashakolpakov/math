import OAI.RepresentationTheory.Theta.Geometric.Cubical.Arguments

/-! # Coordinate Nonvanishing -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! At every triple period point, one explicit product coordinate on
each side of the cubical identity is nonzero. -/

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.exists_coordinate_nonzero (z : Φ.space) : ∃ i, F.coordinate i z ≠ 0 := by
  obtain ⟨s, hs, hsz⟩ := F.nonzero z
  obtain ⟨i, rfl⟩ := F.coordinate_surjective s hs
  exact ⟨i, hsz⟩

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeLeftSection_nonzero (z : Φ.triple.space) :
    ∃ i : Fin 4 → Fin (F.projectiveDimension + 1), F.cubeLeftSection i z ≠ 0 := by
  obtain ⟨i0, h0⟩ := F.exists_coordinate_nonzero (Φ.tripleFirst z + Φ.tripleSecond z + Φ.tripleThird z)
  obtain ⟨i1, h1⟩ := F.exists_coordinate_nonzero (Φ.tripleFirst z)
  obtain ⟨i2, h2⟩ := F.exists_coordinate_nonzero (Φ.tripleSecond z)
  obtain ⟨i3, h3⟩ := F.exists_coordinate_nonzero (Φ.tripleThird z)
  refine ⟨![i0, i1, i2, i3], ?_⟩
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) h2) h3

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeRightSection_nonzero (hJ : J.IsCubical) (z : Φ.triple.space) :
    ∃ i : Fin 3 → Fin (F.projectiveDimension + 1), F.cubeRightSection hJ i z ≠ 0 := by
  obtain ⟨i0, h0⟩ := F.exists_coordinate_nonzero (Φ.tripleFirst z + Φ.tripleSecond z)
  obtain ⟨i1, h1⟩ := F.exists_coordinate_nonzero (Φ.tripleFirst z + Φ.tripleThird z)
  obtain ⟨i2, h2⟩ := F.exists_coordinate_nonzero (Φ.tripleSecond z + Φ.tripleThird z)
  refine ⟨![i0, i1, i2], ?_⟩
  rw [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeRightSection, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.rightCubeOnLeft_apply]
  exact mul_ne_zero (mul_ne_zero h0 h1) h2

end

end OAI.RepresentationTheory.Theta.Geometric
