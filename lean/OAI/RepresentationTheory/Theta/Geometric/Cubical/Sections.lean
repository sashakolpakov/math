import OAI.RepresentationTheory.Theta.Geometric.Cubical.Families
import OAI.RepresentationTheory.Theta.Geometric.AutomorphicFamilyProducts

/-! # Sections -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The products of specified original theta sections are actual
members of the two generated cubical families, with exact values. -/

variable {Φ Ψ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {n : ℕ}
    (f g h : Ψ.space →L[ℂ] Φ.space)
    (hf : ∀ l : Ψ.periodIntegerLattice, f l.val ∈ Φ.periodIntegerLattice)
    (hg : ∀ l : Ψ.periodIntegerLattice, g l.val ∈ Φ.periodIntegerLattice)
    (hh : ∀ l : Ψ.periodIntegerLattice, h l.val ∈ Φ.periodIntegerLattice)

section

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.leftCube (s0 s1 s2 s3 : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n) : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section (J.leftCubeFactor f g h hf hg hh) n :=
  (((s0.comap (f + g + h) (Torus.Data.CM.ProjectivePeriodData.latticeLinear_add_mem (f + g) h (Torus.Data.CM.ProjectivePeriodData.latticeLinear_add_mem f g hf hg) hh)).factorMul
    (s1.comap f hf)).factorMul (s2.comap g hg)).factorMul (s3.comap h hh)

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.rightCube (s12 s13 s23 : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n) : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section (J.rightCubeFactor f g h hf hg hh) n :=
  ((s12.comap (f + g) (Torus.Data.CM.ProjectivePeriodData.latticeLinear_add_mem f g hf hg)).factorMul
    (s13.comap (f + h) (Torus.Data.CM.ProjectivePeriodData.latticeLinear_add_mem f h hf hh))).factorMul
      (s23.comap (g + h) (Torus.Data.CM.ProjectivePeriodData.latticeLinear_add_mem g h hg hh))

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.leftCube_apply (s0 s1 s2 s3 : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n) (z : Ψ.space) :
    AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.leftCube f g h hf hg hh s0 s1 s2 s3 z =
      s0 (f z + g z + h z) * s1 (f z) * s2 (g z) * s3 (h z) := rfl

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.rightCube_apply (s12 s13 s23 : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n) (z : Ψ.space) :
    AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.rightCube f g h hf hg hh s12 s13 s23 z =
      s12 (f z + g z) * s13 (f z + h z) * s23 (g z + h z) := rfl

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.rightCubeOnLeft (hJ : J.IsCubical) (s12 s13 s23 : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n) :
    AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section (J.leftCubeFactor f g h hf hg hh) n :=
  (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.rightCube f g h hf hg hh s12 s13 s23).castFactor (J.cubeFactors_eq f g h hf hg hh hJ).symm

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.rightCubeOnLeft_apply (hJ : J.IsCubical) (s12 s13 s23 : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J n) (z : Ψ.space) :
    AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.rightCubeOnLeft f g h hf hg hh hJ s12 s13 s23 z =
      s12 (f z + g z) * s13 (f z + h z) * s23 (g z + h z) := by
  rw [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.rightCubeOnLeft, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.castFactor_apply]
  rfl

end

variable (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.leftCube_mem (s0 s1 s2 s3 : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree)
    (h0 : s0 ∈ F.sections) (h1 : s1 ∈ F.sections) (h2 : s2 ∈ F.sections) (h3 : s3 ∈ F.sections) :
    AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.leftCube f g h hf hg hh s0 s1 s2 s3 ∈ (F.leftCube f g h hf hg hh).sections := by
  dsimp only [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.leftCube, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.leftCubeWithDegree]
  apply AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_mem
  · apply AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_mem
    · apply AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_mem
      · exact AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap_mem _ _ F s0 h0
      · exact AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap_mem _ _ F s1 h1
    · exact AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap_mem _ _ F s2 h2
  · exact AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap_mem _ _ F s3 h3

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.rightCube_mem (s12 s13 s23 : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree)
    (h12 : s12 ∈ F.sections) (h13 : s13 ∈ F.sections) (h23 : s23 ∈ F.sections) :
    AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.rightCube f g h hf hg hh s12 s13 s23 ∈ (F.rightCube f g h hf hg hh).sections := by
  dsimp only [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.rightCube, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.rightCubeWithDegree]
  apply AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_mem
  · apply AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.factorMul_mem
    · exact AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap_mem _ _ F s12 h12
    · exact AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap_mem _ _ F s13 h13
  · exact AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.comap_mem _ _ F s23 h23

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.rightCubeOnLeft_mem (hJ : J.IsCubical) (s12 s13 s23 : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree)
    (h12 : s12 ∈ F.sections) (h13 : s13 ∈ F.sections) (h23 : s23 ∈ F.sections) :
    AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.rightCubeOnLeft f g h hf hg hh hJ s12 s13 s23 ∈ (F.rightCubeOnLeft f g h hf hg hh hJ).sections :=
  AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.castFactor_mem _ _ _ (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.rightCube_mem f g h hf hg hh F s12 s13 s23 h12 h13 h23)

end

end OAI.RepresentationTheory.Theta.Geometric
