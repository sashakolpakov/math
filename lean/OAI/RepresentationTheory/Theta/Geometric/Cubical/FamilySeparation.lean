import OAI.RepresentationTheory.Theta.Geometric.Cubical.Families
import OAI.RepresentationTheory.Theta.Geometric.FactorProductSeparation

/-! # Family Separation -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Each of the three coordinate factors contributes its point and
tangent separation to the generated left cubical family. -/

variable {Φ Ψ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}
    (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (f g h : Ψ.space →L[ℂ] Φ.space)
    (hf : ∀ l : Ψ.periodIntegerLattice, f l.val ∈ Φ.periodIntegerLattice)
    (hg : ∀ l : Ψ.periodIntegerLattice, g l.val ∈ Φ.periodIntegerLattice)
    (hh : ∀ l : Ψ.periodIntegerLattice, h l.val ∈ Φ.periodIntegerLattice)

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.leftCube_detects_coordinates (p v : Ψ.space)
    (hv : (F.comap f hf).Detects p v ∨ (F.comap g hg).Detects p v ∨ (F.comap h hh).Detects p v) :
    (F.leftCube f g h hf hg hh).Detects p v := by
  change ((((F.comap (f + g + h)
    (Torus.Data.CM.ProjectivePeriodData.latticeLinear_add_mem (f + g) h (Torus.Data.CM.ProjectivePeriodData.latticeLinear_add_mem f g hf hg) hh)).factorMul
    (F.comap f hf) rfl).factorMul (F.comap g hg) rfl).factorMul (F.comap h hh) rfl).Detects p v
  rcases hv with h1 | h2 | h3
  · apply AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_detects_left
    apply AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_detects_left
    exact AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_detects_right _ _ _ p v h1
  · apply AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_detects_left
    exact AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_detects_right _ _ _ p v h2
  · exact AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_detects_right _ _ _ p v h3

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.leftCube_separates_coordinates (p q : Ψ.space)
    (hpq : (F.comap f hf).Separates p q ∨ (F.comap g hg).Separates p q ∨ (F.comap h hh).Separates p q) :
    (F.leftCube f g h hf hg hh).Separates p q := by
  change ((((F.comap (f + g + h)
    (Torus.Data.CM.ProjectivePeriodData.latticeLinear_add_mem (f + g) h (Torus.Data.CM.ProjectivePeriodData.latticeLinear_add_mem f g hf hg) hh)).factorMul
    (F.comap f hf) rfl).factorMul (F.comap g hg) rfl).factorMul (F.comap h hh) rfl).Separates p q
  rcases hpq with h1 | h2 | h3
  · apply AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_separates_left
    apply AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_separates_left
    exact AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_separates_right _ _ _ p q h1
  · apply AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_separates_left
    exact AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_separates_right _ _ _ p q h2
  · exact AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_separates_right _ _ _ p q h3

end

end OAI.RepresentationTheory.Theta.Geometric
