import OAI.RepresentationTheory.Theta.Geometric.FamilyPowers

/-! # Extended Coordinates -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Enlarge a theta family by transformed sections while retaining explicit
indices for both coordinate systems and the original embedding properties. -/

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}
  (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (T : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree → AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree)

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.withSectionMap : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J := by
  classical
  exact F.extend (F.sections.image T)

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.withSectionMapOriginalIndex (i : Fin (F.projectiveDimension + 1)) :
    Fin ((F.withSectionMap T).projectiveDimension + 1) := by
  classical
  exact ((F.withSectionMap T).coordinate_surjective (F.coordinate i)
    (F.mem_extend_left _ _ (F.indexEquiv.symm i).property)).choose

def AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.withSectionMapTransformedIndex (i : Fin (F.projectiveDimension + 1)) :
    Fin ((F.withSectionMap T).projectiveDimension + 1) := by
  classical
  exact ((F.withSectionMap T).coordinate_surjective (T (F.coordinate i))
    (F.mem_extend_right _ _ (Finset.mem_image.mpr ⟨F.coordinate i, (F.indexEquiv.symm i).property, rfl⟩))).choose

@[simp]
theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.withSectionMapOriginalIndex_coordinate (i : Fin (F.projectiveDimension + 1)) :
    (F.withSectionMap T).coordinate (F.withSectionMapOriginalIndex T i) = F.coordinate i := by
  classical
  exact ((F.withSectionMap T).coordinate_surjective (F.coordinate i)
    (F.mem_extend_left _ _ (F.indexEquiv.symm i).property)).choose_spec

@[simp]
theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.withSectionMapTransformedIndex_coordinate (i : Fin (F.projectiveDimension + 1)) :
    (F.withSectionMap T).coordinate (F.withSectionMapTransformedIndex T i) = T (F.coordinate i) := by
  classical
  exact ((F.withSectionMap T).coordinate_surjective (T (F.coordinate i))
    (F.mem_extend_right _ _ (Finset.mem_image.mpr ⟨F.coordinate i, (F.indexEquiv.symm i).property, rfl⟩))).choose_spec

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.withSectionMap_injective (hF : Function.Injective F.projectiveMap) :
    Function.Injective (F.withSectionMap T).projectiveMap := F.extend_injective _ hF

theorem AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.withSectionMap_detects (p v : Φ.space) (hF : F.Detects p v) :
    (F.withSectionMap T).Detects p v := F.extend_detects _ p v hF

end

end OAI.RepresentationTheory.Theta.Geometric
