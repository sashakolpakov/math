import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.SectionProjectiveCoordinates

/-! # Coordinate Projective Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.CoordinateProjectivePoints

noncomputable section

/-! The coordinate-axis points and the all-one point are actual sections
of relative projective space. Multiplying all coordinates by a unit
preserves the represented section over any base scheme. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (S : Scheme.{u}) (n : ℕ)

def standardBasisProjectiveCoordinates (i k : Fin (n + 1)) : Γ(S, ⊤) := if i = k then 1 else 0

theorem standardBasisProjectiveCoordinates_cover (i : Fin (n + 1)) :
    ∀ x : S, ∃ k, x ∈ S.basicOpen (standardBasisProjectiveCoordinates S n i k) := by
  intro x
  refine ⟨i, ?_⟩
  simp only [standardBasisProjectiveCoordinates, ite_true]
  exact (S.basicOpen_of_isUnit (isUnit_one : IsUnit (1 : Γ(S, ⊤)))).symm ▸ trivial

def standardBasisProjectivePoint (i : Fin (n + 1)) :
    Over.mk (𝟙 S) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n :=
  Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (standardBasisProjectiveCoordinates S n i)
    (standardBasisProjectiveCoordinates_cover S n i)

theorem allOneProjectiveCoordinates_cover :
    ∀ x : S, ∃ _i : Fin (n + 1), x ∈ S.basicOpen (1 : Γ(S, ⊤)) := by
  intro x
  exact ⟨0, (S.basicOpen_of_isUnit (isUnit_one : IsUnit (1 : Γ(S, ⊤)))).symm ▸ trivial⟩

def allOneProjectivePoint : Over.mk (𝟙 S) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n :=
  Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (fun _ : Fin (n + 1) => (1 : Γ(S, ⊤)))
    (allOneProjectiveCoordinates_cover S n)

theorem scalarCoordinateProjectivePoint_unit_mul
    (v : Fin (n + 1) → Γ(S, ⊤)) (u : Γ(S, ⊤)ˣ)
    (hv : ∀ x : S, ∃ i, x ∈ S.basicOpen (v i))
    (hu : ∀ x : S, ∃ i, x ∈ S.basicOpen ((u : Γ(S, ⊤)) * v i)) :
    Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (fun i => (u : Γ(S, ⊤)) * v i) hu =
      Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint v hv := by
  let a := (Global.Sections.structureModuleEndRingEquiv S).symm (u : Γ(S, ⊤))
  have ha : IsIso a := (Global.Sections.structureModuleEnd_isIso_iff a).mpr (by
    change IsUnit (Global.Sections.structureModuleEndRingEquiv S ((Global.Sections.structureModuleEndRingEquiv S).symm (u : Γ(S, ⊤))))
    rw [RingEquiv.apply_symm_apply]
    exact u.isUnit)
  let e := asIso a
  let hve := Section.ProjectiveTargetIso.sections_compIso_covers e (Family.SectionProjectiveCoordinates.scalarCoordinateSections v) (Family.SectionProjectiveCoordinates.scalarCoordinateSections_cover v hv)
  have he : (fun i => Family.SectionProjectiveCoordinates.scalarCoordinateSections v i ≫ e.hom) =
      Family.SectionProjectiveCoordinates.scalarCoordinateSections (fun i => (u : Γ(S, ⊤)) * v i) := by
    funext i
    apply (Global.Sections.structureModuleEndRingEquiv S).injective
    change Global.Sections.structureModuleEndRingEquiv S (a * Family.SectionProjectiveCoordinates.scalarCoordinateSections v i) =
      Global.Sections.structureModuleEndRingEquiv S ((Global.Sections.structureModuleEndRingEquiv S).symm ((u : Γ(S, ⊤)) * v i))
    rw [map_mul, RingEquiv.apply_symm_apply]
    change (u : Γ(S, ⊤)) *
      Global.Sections.structureModuleEndRingEquiv S ((Global.Sections.structureModuleEndRingEquiv S).symm (v i)) = _
    rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  symm
  exact (Section.ProjectiveTargetIso.sectionProjectiveMorphism_targetIso (𝟙 S) e (Family.SectionProjectiveCoordinates.scalarCoordinateSections v)
    (Family.SectionProjectiveCoordinates.scalarCoordinateSections_cover v hv) hve).trans
      (Section.ProjectiveTargetIso.sectionProjectiveMorphism_congr (𝟙 S) he hve (Family.SectionProjectiveCoordinates.scalarCoordinateSections_cover _ hu))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.CoordinateProjectivePoints
