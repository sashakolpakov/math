import OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneTransitions
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OverFrame
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionOverlap
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OverSection
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineSectionOf

/-! # Projective Coordinates App -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp

noncomputable section

/-! All homogeneous coordinates as sections of one actual hyperplane line bundle. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

namespace Construction.ProjectiveCoordinates

variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) := fun U => by
  change IsMulCommutative (X.presheaf.obj U)
  exact IsMulCommutative.of_comm fun a b => mul_comm a b

open _root_.MvPolynomial

def bundle (j : σ) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Proj (homogeneousSubmodule σ R)) where
  sheaf := SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j
  locallyTrivial x := by
    obtain ⟨ι, U, hU, he⟩ := SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf_isInvertible (R := R) j
    have hx : x ∈ iSup U := hU.symm ▸ (show x ∈ (⊤ : (Proj _).Opens) from trivial)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨U i, hi, he i⟩

def frame (i j : σ) :
    (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j).over (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) ≅
      _root_.SheafOfModules.unit
        ((Proj (homogeneousSubmodule σ R)).ringCatSheaf.over (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)) :=
  SheafCohomology.Projective.Dual.SheafOfModules.dualOverIsoOfIso
    (Proj (homogeneousSubmodule σ R)).ringCatSheaf
    (SheafCohomology.Projective.IdealModule.idealModule (SheafCohomology.Projective.SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)) (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    (SheafCohomology.Projective.HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization (R := R) i j)

theorem frame_transition (i k j : σ) :
    SheafCohomology.Projective.DualFrameTransition.FrameTransition (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization
      (Proj (homogeneousSubmodule σ R)).ringCatSheaf (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j)
      (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (frame (R := R) i j)
      (Over.mk (homOfLE (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k))))
    (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization
      (Proj (homogeneousSubmodule σ R)).ringCatSheaf (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j)
      (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k) (frame (R := R) k j)
      (Over.mk (homOfLE (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k))))
      (SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd _ _
        (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k : Γ(Proj _, SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k))) := by
  exact OverFrame.Construction.OverFrameTransitions.dual_chosen (X := Proj (homogeneousSubmodule σ R))
    (SheafCohomology.Projective.IdealModule.idealModule (SheafCohomology.Projective.SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)
    (SheafCohomology.Projective.HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization (R := R) i j)
    (SheafCohomology.Projective.HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization (R := R) k j)
    (frame (R := R) i j) (frame (R := R) k j) rfl rfl
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k : Γ(Proj _, SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k))
    (SheafCohomology.Projective.HyperplaneTransitions.MvPolynomial.coordinateHyperplaneIdealOver_restrict_transition (R := R) i k j)

def localSection (i j k : σ) :
    Γ((SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j), SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) :=
  SheafCohomology.Projective.FrameSections.overTrivializationSection (X := Proj (homogeneousSubmodule σ R))
    (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j) (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (frame (R := R) i j)
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i k)

theorem localSection_compatible (i l j k : σ) :
    (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j).presheaf.map
      (homOfLE (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i l)).op (localSection (R := R) i j k) =
    (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j).presheaf.map
      (homOfLE (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i l)).op (localSection (R := R) l j k) := by
  exact OverFrame.Construction.OverFrameTransitions.sections (X := Proj (homogeneousSubmodule σ R)) (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j)
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i l)
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i l)
    (frame (R := R) i j) (frame (R := R) l j)
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i k) (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) l k)
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i l : Γ(Proj _, SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i l))
    (frame_transition (R := R) i l j)
    ((SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_restrict_eq_transition_mul (R := R) i l k).trans
      (mul_comm _ _))

theorem exists_section (j k : σ) :
    ∃ s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Proj (homogeneousSubmodule σ R)) ⟶ (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j),
      ∀ i, s.app (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (1 : Γ(Proj _, SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)) =
        localSection (R := R) i j k := by
  apply ExistsUnique.exists
  apply SectionOverlap.Construction.SectionOverlapGluing.glue (X := Proj (homogeneousSubmodule σ R)) _ (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R)) _
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R)) (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R))
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R)) (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq (R := R))
  · intro i l
    exact localSection_compatible (R := R) i l j k
  · intro x
    apply TopologicalSpace.Opens.mem_iSup.mp
    rw [SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]
    trivial

def sectionHom (j k : σ) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Proj (homogeneousSubmodule σ R)) ⟶ (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j) :=
  (exists_section j k).choose

theorem sectionHom_app (i j k : σ) :
    (ProjectiveCoordinates.sectionHom (R := R) j k).app (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (1 : Γ(Proj _, SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)) =
      localSection (R := R) i j k :=
  (exists_section j k).choose_spec i

theorem sectionHom_coordinate (i j k : σ) :
    (ProjectiveCoordinates.sectionHom (R := R) j k).over (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) ≫ (frame (R := R) i j).hom =
      SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd
        (Proj (homogeneousSubmodule σ R)).ringCatSheaf (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
        (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i k) := by
  apply OverSection.Construction.OverSectionLocus.coordinate_eq (X := Proj (homogeneousSubmodule σ R))
  rw [sectionHom_app]
  exact SheafCohomology.Projective.FrameSections.overTrivializationSection_coefficient (X := Proj (homogeneousSubmodule σ R)) _ _ _ _

theorem sectionHom_nonvanishing (j k : σ) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (ProjectiveCoordinates.sectionHom (R := R) j k) = SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k := by
  have h (i : σ) :
      AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (ProjectiveCoordinates.sectionHom (R := R) j k) ⊓ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i =
        SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i ⊓ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k :=
    (OverSection.Construction.OverSectionLocus.nonvanishing (X := Proj (homogeneousSubmodule σ R)) _ _ (frame (R := R) i j) _ (sectionHom_coordinate (R := R) i j k)).trans
      ((SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_basicOpen (R := R) i k).trans
        (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq (R := R) i k))
  apply TopologicalSpace.Opens.ext
  ext x
  change x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (ProjectiveCoordinates.sectionHom (R := R) j k) ↔ x ∈ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k
  have hx : x ∈ iSup (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) : σ → (Proj _).Opens) := by
    rw [SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hh := congrArg (fun U : (Proj (homogeneousSubmodule σ R)).Opens => x ∈ U) (h i)
  simpa only [TopologicalSpace.Opens.mem_inf, hi, and_true, true_and] using hh.to_iff

def sectionCover [Fintype σ] (j : σ) :
    AffineSectionOf.Construction.AffineSectionCover.Data (Proj (homogeneousSubmodule σ R)) where
  lineBundle := bundle (R := R) j
  I := σ
  sectionHom := ProjectiveCoordinates.sectionHom (R := R) j
  covers x := by
    have hx : x ∈ iSup (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) : σ → (Proj _).Opens) := by
      rw [SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨i, (sectionHom_nonvanishing (R := R) j i).symm ▸ hi⟩
  affine i := by
    change IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (ProjectiveCoordinates.sectionHom (R := R) j i))
    rw [sectionHom_nonvanishing]
    exact SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen (R := R) i

end Construction.ProjectiveCoordinates

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp
