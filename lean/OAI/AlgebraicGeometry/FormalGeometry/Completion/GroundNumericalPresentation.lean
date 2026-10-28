import OAI.AlgebraicGeometry.FormalGeometry.Completion.GroundGeometricallyAmple
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.HilbertDifference

/-! # Ground Numerical Presentation -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.GroundNumericalPresentation

noncomputable section

/-! Numerical data for the geometric group, built from a ground-field
bundle whose ampleness, global generation, and symmetry have been proved. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.Obj

namespace Construction

universe u

variable (K : Type u) [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A]

structure GroundGeometricAmpleBundle where
  bundle : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left
  ample : (bundle.pullback (pullback.fst A.hom (Geometric.Frobenius.Construction.algebraicClosureBase K))).IsAmple
  frames : Frame.SectionDetection.Construction.HasFrameSections (bundle.pullback (pullback.fst A.hom (Geometric.Frobenius.Construction.algebraicClosureBase K))).sheaf
  symmetric : Nonempty ((bundle.pullback (GrpObj.inv (X := A)).left).sheaf ≅ bundle.sheaf)

variable [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]

def groundGeometricAmpleBundle : GroundGeometricAmpleBundle K A := by
  apply Classical.choice
  obtain ⟨L, hL, hg, hs⟩ := GroundGeometricallyAmple.Construction.exists_ground_geometrically_generated_ample_symmetric_lineBundle K A
  exact ⟨⟨L, hL, hg, hs⟩⟩

def groundGeometricNumericalPresentation : Endomorphism.HilbertDifference.Construction.EndomorphismNumericalPresentation (Geometric.Frobenius.Construction.geometricFiberOver K A) := by
  let B := Geometric.Frobenius.Construction.geometricFiberOver K A
  have : IsProper B.hom := inferInstanceAs (IsProper (pullback.snd A.hom (Geometric.Frobenius.Construction.algebraicClosureBase K)))
  have : Smooth B.hom := inferInstanceAs (Smooth (pullback.snd A.hom (Geometric.Frobenius.Construction.algebraicClosureBase K)))
  have : GeometricallyIntegral B.hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd A.hom (Geometric.Frobenius.Construction.algebraicClosureBase K)))
  let G := groundGeometricAmpleBundle K A
  exact {
    projective := (Geometric.Projectivity.Construction.geometric_group_projectivePresentation B).some
    bundle := G.bundle.pullback (pullback.fst A.hom (Geometric.Frobenius.Construction.algebraicClosureBase K))
    ample := G.ample
    frames := G.frames
    symmetric := Geometric.LineBundleInvariance.Construction.geometricLineBundle_symmetric K A G.bundle G.symmetric }

theorem groundGeometricNumericalPresentation_bundle :
    (groundGeometricNumericalPresentation K A).bundle =
      (groundGeometricAmpleBundle K A).bundle.pullback (pullback.fst A.hom (Geometric.Frobenius.Construction.algebraicClosureBase K)) := rfl

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.GroundNumericalPresentation
