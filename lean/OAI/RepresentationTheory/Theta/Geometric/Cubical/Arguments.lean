import OAI.RepresentationTheory.Theta.Geometric.Cubical.Sections
import OAI.RepresentationTheory.Theta.Geometric.CommonCubicalEmbedding

/-! # Arguments -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! Explicit indices in the common cubical embedding retain the
products of the original theta coordinates on both sides. -/

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hJ : J.IsCubical)

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeLeftSection (i : Fin 4 → Fin (F.projectiveDimension + 1)) :
    AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section (J.leftCubeFactor Φ.tripleFirst Φ.tripleSecond Φ.tripleThird
      Φ.tripleFirst_mem Φ.tripleSecond_mem Φ.tripleThird_mem) F.degree :=
  AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.leftCube Φ.tripleFirst Φ.tripleSecond Φ.tripleThird
    Φ.tripleFirst_mem Φ.tripleSecond_mem Φ.tripleThird_mem
    (F.coordinate (i 0)) (F.coordinate (i 1)) (F.coordinate (i 2)) (F.coordinate (i 3))

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeRightSection (i : Fin 3 → Fin (F.projectiveDimension + 1)) :
    AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section (J.leftCubeFactor Φ.tripleFirst Φ.tripleSecond Φ.tripleThird
      Φ.tripleFirst_mem Φ.tripleSecond_mem Φ.tripleThird_mem) F.degree :=
  AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.rightCubeOnLeft Φ.tripleFirst Φ.tripleSecond Φ.tripleThird
    Φ.tripleFirst_mem Φ.tripleSecond_mem Φ.tripleThird_mem hJ
    (F.coordinate (i 0)) (F.coordinate (i 1)) (F.coordinate (i 2))

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeLeftSection_mem (i : Fin 4 → Fin (F.projectiveDimension + 1)) :
    F.cubeLeftSection i ∈ (F.commonTripleCube hJ).sections :=
  F.tripleCube.mem_extend_left _ _ (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.leftCube_mem Φ.tripleFirst Φ.tripleSecond Φ.tripleThird
    Φ.tripleFirst_mem Φ.tripleSecond_mem Φ.tripleThird_mem F _ _ _ _
    (F.indexEquiv.symm (i 0)).property (F.indexEquiv.symm (i 1)).property
    (F.indexEquiv.symm (i 2)).property (F.indexEquiv.symm (i 3)).property)

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeRightSection_mem (i : Fin 3 → Fin (F.projectiveDimension + 1)) :
    F.cubeRightSection hJ i ∈ (F.commonTripleCube hJ).sections :=
  AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.extendFamily_mem_right _ _ _ _ (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.rightCubeOnLeft_mem Φ.tripleFirst Φ.tripleSecond Φ.tripleThird
    Φ.tripleFirst_mem Φ.tripleSecond_mem Φ.tripleThird_mem F hJ _ _ _
    (F.indexEquiv.symm (i 0)).property (F.indexEquiv.symm (i 1)).property
    (F.indexEquiv.symm (i 2)).property)

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeLeftIndex (i : Fin 4 → Fin (F.projectiveDimension + 1)) :
    Fin ((F.commonTripleCube hJ).projectiveDimension + 1) :=
  ((F.commonTripleCube hJ).coordinate_surjective (F.cubeLeftSection i) (F.cubeLeftSection_mem hJ i)).choose

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeRightIndex (i : Fin 3 → Fin (F.projectiveDimension + 1)) :
    Fin ((F.commonTripleCube hJ).projectiveDimension + 1) :=
  ((F.commonTripleCube hJ).coordinate_surjective (F.cubeRightSection hJ i) (F.cubeRightSection_mem hJ i)).choose

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeLeftIndex_coordinate (i : Fin 4 → Fin (F.projectiveDimension + 1)) :
    (F.commonTripleCube hJ).coordinate (F.cubeLeftIndex hJ i) = F.cubeLeftSection i :=
  ((F.commonTripleCube hJ).coordinate_surjective (F.cubeLeftSection i) (F.cubeLeftSection_mem hJ i)).choose_spec

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeRightIndex_coordinate (i : Fin 3 → Fin (F.projectiveDimension + 1)) :
    (F.commonTripleCube hJ).coordinate (F.cubeRightIndex hJ i) = F.cubeRightSection hJ i :=
  ((F.commonTripleCube hJ).coordinate_surjective (F.cubeRightSection hJ i) (F.cubeRightSection_mem hJ i)).choose_spec

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeLeftIndex_value (i : Fin 4 → Fin (F.projectiveDimension + 1)) (z : Φ.triple.space) :
    (F.commonTripleCube hJ).coordinate (F.cubeLeftIndex hJ i) z =
      F.coordinate (i 0) (Φ.tripleFirst z + Φ.tripleSecond z + Φ.tripleThird z) *
      F.coordinate (i 1) (Φ.tripleFirst z) * F.coordinate (i 2) (Φ.tripleSecond z) *
      F.coordinate (i 3) (Φ.tripleThird z) := by
  rw [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeLeftIndex_coordinate]
  rfl

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeRightIndex_value (i : Fin 3 → Fin (F.projectiveDimension + 1)) (z : Φ.triple.space) :
    (F.commonTripleCube hJ).coordinate (F.cubeRightIndex hJ i) z =
      F.coordinate (i 0) (Φ.tripleFirst z + Φ.tripleSecond z) *
      F.coordinate (i 1) (Φ.tripleFirst z + Φ.tripleThird z) *
      F.coordinate (i 2) (Φ.tripleSecond z + Φ.tripleThird z) := by
  rw [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeRightIndex_coordinate]
  exact AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.rightCubeOnLeft_apply _ _ _ _ _ _ _ _ _ _ _

end

/-! The seven arguments of the original theta coordinates in the
cubical comparison. -/

section

def Torus.Data.CM.ProjectivePeriodData.cubePositiveArgument (Φ : Torus.Data.CM.ProjectivePeriodData) (k : Fin 4) (z : Φ.triple.space) : Φ.space :=
  ![Φ.tripleFirst z + Φ.tripleSecond z + Φ.tripleThird z,
    Φ.tripleFirst z, Φ.tripleSecond z, Φ.tripleThird z] k

def Torus.Data.CM.ProjectivePeriodData.cubeNegativeArgument (Φ : Torus.Data.CM.ProjectivePeriodData) (k : Fin 3) (z : Φ.triple.space) : Φ.space :=
  ![Φ.tripleFirst z + Φ.tripleSecond z, Φ.tripleFirst z + Φ.tripleThird z,
    Φ.tripleSecond z + Φ.tripleThird z] k

end

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hJ : J.IsCubical)

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeLeftSection_value_prod (i : Fin 4 → Fin (F.projectiveDimension + 1)) (z : Φ.triple.space) :
    F.cubeLeftSection i z = ∏ k, F.coordinate (i k) (Φ.cubePositiveArgument k z) := by
  change F.coordinate (i 0) (Φ.tripleFirst z + Φ.tripleSecond z + Φ.tripleThird z) *
    F.coordinate (i 1) (Φ.tripleFirst z) * F.coordinate (i 2) (Φ.tripleSecond z) *
    F.coordinate (i 3) (Φ.tripleThird z) = _
  simp [Torus.Data.CM.ProjectivePeriodData.cubePositiveArgument, Fin.prod_univ_succ, mul_assoc]

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeRightSection_value_prod (j : Fin 3 → Fin (F.projectiveDimension + 1)) (z : Φ.triple.space) :
    F.cubeRightSection hJ j z = ∏ k, F.coordinate (j k) (Φ.cubeNegativeArgument k z) := by
  rw [← F.cubeRightIndex_coordinate hJ j, F.cubeRightIndex_value hJ j z]
  simp [Torus.Data.CM.ProjectivePeriodData.cubeNegativeArgument, Fin.prod_univ_succ, mul_assoc]

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeLeftSection_ne_zero_iff (i : Fin 4 → Fin (F.projectiveDimension + 1)) (z : Φ.triple.space) :
    F.cubeLeftSection i z ≠ 0 ↔ ∀ k, F.coordinate (i k) (Φ.cubePositiveArgument k z) ≠ 0 := by
  rw [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeLeftSection_value_prod]
  simp only [Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const]

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeRightSection_ne_zero_iff (j : Fin 3 → Fin (F.projectiveDimension + 1)) (z : Φ.triple.space) :
    F.cubeRightSection hJ j z ≠ 0 ↔ ∀ k, F.coordinate (j k) (Φ.cubeNegativeArgument k z) ≠ 0 := by
  rw [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeRightSection_value_prod]
  simp only [Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const]

end

end OAI.RepresentationTheory.Theta.Geometric
