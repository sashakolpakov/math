import OAI.RepresentationTheory.Theta.Geometric.FamilyPowers

/-! # Common Power -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! A single embedding contains pure powers of the coordinates of two
theta embeddings in their common degree. -/

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonPower_degree_eq : (G.power F.degree).degree = (F.power G.degree).degree := by
  simp only [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.power_degree, Nat.mul_comm]

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonPower : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J := by
  classical
  exact (F.power G.degree).extend
    ((G.power F.degree).sections.image (AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section.redegree (F.commonPower_degree_eq G)))

@[simp]
theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonPower_degree : (F.commonPower G).degree = F.degree * G.degree :=
  F.power_degree G.degree

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonPower_injective (hG : 0 < G.degree) (hF : Function.Injective F.projectiveMap) :
    Function.Injective (F.commonPower G).projectiveMap :=
  (F.power G.degree).extend_injective _ (F.power_injective G.degree hG hF)

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonPower_detects (hG : 0 < G.degree) (p v : Φ.space) (hF : F.Detects p v) :
    (F.commonPower G).Detects p v :=
  (F.power G.degree).extend_detects _ p v (F.power_detects G.degree hG p v hF)

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonPower_left_coordinate (i : Fin (F.projectiveDimension + 1)) :
    ∃ k : Fin ((F.commonPower G).projectiveDimension + 1),
      ∀ z, (F.commonPower G).coordinate k z = F.coordinate i z ^ G.degree := by
  classical
  let s := F.powerSection (F.coordinate i) G.degree
  have hs : s ∈ (F.commonPower G).sections :=
    (F.power G.degree).mem_extend_left _ s
      (F.powerSection_mem (F.coordinate i) (F.indexEquiv.symm i).property G.degree)
  obtain ⟨k, hk⟩ := (F.commonPower G).coordinate_surjective s hs
  refine ⟨k, fun z => ?_⟩
  rw [hk]
  exact F.powerSection_apply (F.coordinate i) G.degree z

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonPower_right_coordinate (j : Fin (G.projectiveDimension + 1)) :
    ∃ k : Fin ((F.commonPower G).projectiveDimension + 1),
      ∀ z, (F.commonPower G).coordinate k z = G.coordinate j z ^ F.degree := by
  classical
  let t := G.powerSection (G.coordinate j) F.degree
  let s := t.redegree (F.commonPower_degree_eq G)
  have ht : t ∈ (G.power F.degree).sections :=
    G.powerSection_mem (G.coordinate j) (G.indexEquiv.symm j).property F.degree
  have hs : s ∈ (F.commonPower G).sections :=
    (F.power G.degree).mem_extend_right _ s (Finset.mem_image.mpr ⟨t, ht, rfl⟩)
  obtain ⟨k, hk⟩ := (F.commonPower G).coordinate_surjective s hs
  refine ⟨k, fun z => ?_⟩
  rw [hk]
  exact G.powerSection_apply (G.coordinate j) F.degree z

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonPowerLeftIndex (i : Fin (F.projectiveDimension + 1)) :
    Fin ((F.commonPower G).projectiveDimension + 1) :=
  (F.commonPower_left_coordinate G i).choose

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonPowerRightIndex (j : Fin (G.projectiveDimension + 1)) :
    Fin ((F.commonPower G).projectiveDimension + 1) :=
  (F.commonPower_right_coordinate G j).choose

@[simp]
theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonPowerLeftIndex_coordinate (i : Fin (F.projectiveDimension + 1)) (z : Φ.space) :
    (F.commonPower G).coordinate (F.commonPowerLeftIndex G i) z = F.coordinate i z ^ G.degree :=
  (F.commonPower_left_coordinate G i).choose_spec z

@[simp]
theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonPowerRightIndex_coordinate (j : Fin (G.projectiveDimension + 1)) (z : Φ.space) :
    (F.commonPower G).coordinate (F.commonPowerRightIndex G j) z = G.coordinate j z ^ F.degree :=
  (F.commonPower_right_coordinate G j).choose_spec z

end

end OAI.RepresentationTheory.Theta.Geometric
