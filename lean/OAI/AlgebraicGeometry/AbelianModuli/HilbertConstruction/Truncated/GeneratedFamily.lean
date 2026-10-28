import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GeneratedParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.UniversalFinitePresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.FinitePersistence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Generated Family -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GeneratedFamily

noncomputable section

/-! Restricting the actual universal projective family to the finite generation locus. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (S : Scheme.{u}) (n B : ℕ) (r : ℕ → ℕ) (N : ℕ)

def truncatedGeneratedFamily : Over (GeneratedParameters.truncatedGeneratedParameters S n B r N).left :=
  (Over.pullback (GeneratedParameters.truncatedGeneratedInclusion S n B r N).left).obj
    (UniversalIdeal.truncatedUniversalFamily S n B r)

def truncatedGeneratedProjectivePresentation : Projective.ProjectivePresentations.ProjectivePresentation (truncatedGeneratedFamily S n B r N) :=
  (UniversalIdeal.truncatedUniversalProjectivePresentation S n B r).baseChange
    (GeneratedParameters.truncatedGeneratedInclusion S n B r N).left

theorem truncatedGeneratedFamily_proper : IsProper (truncatedGeneratedFamily S n B r N).hom :=
  (truncatedGeneratedProjectivePresentation S n B r N).proper

theorem truncatedGeneratedFamily_locallyFinitePresentation :
    LocallyOfFinitePresentation (truncatedGeneratedFamily S n B r N).hom := by
  have := UniversalFinitePresentation.truncatedUniversalFamily_locallyFinitePresentation S n B r
  change LocallyOfFinitePresentation
    (pullback.snd (UniversalIdeal.truncatedUniversalFamily S n B r).hom (GeneratedParameters.truncatedGeneratedInclusion S n B r N).left)
  infer_instance

variable {S n B r N} {R : CommRingCat.{u}}

def truncatedGeneratedFamilyAffineIso (x : Spec R ⟶ (GeneratedParameters.truncatedGeneratedParameters S n B r N).left) :
    (AffineUniversalData.truncatedAffineUniversalData (x ≫ (GeneratedParameters.truncatedGeneratedInclusion S n B r N).left)).projectiveFamily ≅
      (Over.pullback x).obj (truncatedGeneratedFamily S n B r N) :=
  UniversalFamilyCharts.truncatedUniversalFamilyAffineIso (x ≫ (GeneratedParameters.truncatedGeneratedInclusion S n B r N).left) ≪≫
    (Over.pullbackComp x (GeneratedParameters.truncatedGeneratedInclusion S n B r N).left).app
      (UniversalIdeal.truncatedUniversalFamily S n B r)

theorem truncatedGeneratedAffineData_condition
    (x : Spec R ⟶ (GeneratedParameters.truncatedGeneratedParameters S n B r N).left) :
    (AffineUniversalData.truncatedAffineUniversalData (x ≫ (GeneratedParameters.truncatedGeneratedInclusion S n B r N).left)).GeneratedFromDegree N := by
  apply (GenerationPointCriterion.truncatedGeneratedOpen_affine_point_iff
    (Over.homMk (x ≫ (GeneratedParameters.truncatedGeneratedInclusion S n B r N).left) rfl) N).mp
  rintro _ ⟨t, rfl⟩
  exact (x t).property

theorem truncatedGeneratedFamily_flat (hB : FinitePersistence.truncatedFlatnessBound n N ≤ B) :
    Flat (truncatedGeneratedFamily S n B r N).hom := by
  let : IsZariskiLocalAtTarget (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{u}) (Q := RingHom.Flat)
  let C := (GeneratedParameters.truncatedGeneratedParameters S n B r N).left.affineOpenCover
  apply IsZariskiLocalAtTarget.of_openCover (P := @Flat) C.openCover
  intro i
  let x := C.f i
  let D := AffineUniversalData.truncatedAffineUniversalData (x ≫ (GeneratedParameters.truncatedGeneratedInclusion S n B r N).left)
  have : Flat D.projectiveFamily.hom :=
    D.projectiveFamily_flat_of_generatedFromDegree N hB (truncatedGeneratedAffineData_condition x)
  let e := truncatedGeneratedFamilyAffineIso x
  have : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  have hh : Flat (e.inv.left ≫ D.projectiveFamily.hom) := inferInstance
  have he : e.inv.left ≫ D.projectiveFamily.hom =
      C.openCover.pullbackHom (truncatedGeneratedFamily S n B r N).hom i := e.inv.w
  exact he ▸ hh

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GeneratedFamily
