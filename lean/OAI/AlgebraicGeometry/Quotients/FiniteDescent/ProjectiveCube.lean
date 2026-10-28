import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineNeighborhoodTrivial
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductFrames
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PointedAffineCover
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AbelianGeometric

/-! # Projective Cube -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCube

noncomputable section

/-! The cube bundle is trivial when the first two factors admit affine
section covers, with the proper smooth group retained as the third factor. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj

universe u

namespace Construction.ProjectiveCubeTriviality

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductFrames.Construction.CubeProductCoordinates

variable {K : Type u} [Field K] [IsAlgClosed K] (A : Over (Spec (.of K)))
variable [GrpObj A] [IsCommMonObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
variable {B C : Scheme.{u}} (b : B ⟶ Spec (.of K)) (c : C ⟶ Spec (.of K))
variable [IsProper b] [IsProper c] [GeometricallyIntegral b] [GeometricallyIntegral c]
variable (DB : AffineSectionOf.Construction.AffineSectionCover.Data B) (DC : AffineSectionOf.Construction.AffineSectionCover.Data C)
variable (u : B ⟶ A.left) (hu : u ≫ A.hom = b) (v : C ⟶ A.left) (hv : v ≫ A.hom = c)
variable (sB : Spec (.of K) ⟶ B) (hsB : sB ≫ b = 𝟙 _) (hB : sB ≫ u = CubeProductFrames.Construction.CubeProductCoordinates.origin A)
variable (sC : Spec (.of K) ⟶ C) (hsC : sC ≫ c = 𝟙 _) (hC : sC ≫ v = CubeProductFrames.Construction.CubeProductCoordinates.origin A)
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)

include DB DC hsB hB hsC hC

theorem trivial : Nonempty ((CubeProductFrames.Construction.CubeProductCoordinates.cubeBundle A b c u hu v hv L).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (CubeProductBase.Construction.CubeProductCoordinates.total A b c)) := by
  have : GeometricallyIntegral A.hom := AbelianGeometric.Construction.AbelianGeometricIntegral.geometricallyIntegral A
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : IsIntegral B := GeometricallyIntegral.isIntegral_of_subsingleton b
  have : IsIntegral C := GeometricallyIntegral.isIntegral_of_subsingleton c
  have : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace b
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  let U := PointedAffineCover.Construction.PointedFiniteAffineCover.ofIntegral sB
  let V := PointedAffineCover.Construction.PointedFiniteAffineCover.ofIntegral sC
  let : Fintype U.I := U.fintype
  let : LinearOrder U.I := U.linearOrder
  let : Fintype V.I := V.fintype
  let : LinearOrder V.I := V.linearOrder
  have hi : ⊤ ≤ CubeProductBase.Construction.CubeProductCoordinates.familyPoint A b sB hsB ⁻¹ᵁ
      (pullback.fst b A.hom ⁻¹ᵁ U.opens U.distinguished) := by
    change ⊤ ≤ (CubeProductBase.Construction.CubeProductCoordinates.familyPoint A b sB hsB ≫ pullback.fst b A.hom) ⁻¹ᵁ U.opens U.distinguished
    rw [CubeProductBase.Construction.CubeProductCoordinates.familyPoint, pullback.lift_fst]
    exact fun x _ => U.point_in (show A.hom x ∈ (⊤ : (Spec (.of K)).Opens) from True.intro)
  have hj : ⊤ ≤ CubeProductBase.Construction.CubeProductCoordinates.familyPoint A c sC hsC ⁻¹ᵁ
      (pullback.fst c A.hom ⁻¹ᵁ V.opens V.distinguished) := by
    change ⊤ ≤ (CubeProductBase.Construction.CubeProductCoordinates.familyPoint A c sC hsC ≫ pullback.fst c A.hom) ⁻¹ᵁ V.opens V.distinguished
    rw [CubeProductBase.Construction.CubeProductCoordinates.familyPoint, pullback.lift_fst]
    exact fun x _ => V.point_in (show A.hom x ∈ (⊤ : (Spec (.of K)).Opens) from True.intro)
  have hN (x : A.left) : ∃ W : A.left.Opens, IsAffineOpen W ∧ x ∈ W ∧
      RationalPoint.Construction.RationalPointResidue.point (CubeProductFrames.Construction.CubeProductCoordinates.origin A) ∈ W := by
    obtain ⟨W, hW, hsub⟩ := GroupIrreducibleOf.Construction.GroupIrreducible.exists_affineOpen_of_finite A
      {x, RationalPoint.Construction.RationalPointResidue.point (CubeProductFrames.Construction.CubeProductCoordinates.origin A)} ((Set.finite_singleton _).insert x)
    exact ⟨W, hW, hsub (by simp), hsub (by simp)⟩
  exact AffineNeighborhoodTrivial.Construction.AffineNeighborhoodSeesaw.trivial b c DB DC (CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (CubeProductBase.Construction.CubeProductCoordinates.rightBase A c)
    (pullback.fst b A.hom) (pullback.fst c A.hom) A.hom
    (IsPullback.of_hasPullback b A.hom) (IsPullback.of_hasPullback c A.hom)
    U.opens V.opens U.affine V.affine U.covers V.covers
    (CubeProductBase.Construction.CubeProductCoordinates.familyPoint A b sB hsB) (CubeProductBase.Construction.CubeProductCoordinates.familyPoint_over A b sB hsB)
    (CubeProductBase.Construction.CubeProductCoordinates.familyPoint A c sC hsC) (CubeProductBase.Construction.CubeProductCoordinates.familyPoint_over A c sC hsC)
    U.distinguished hi V.distinguished hj (CubeProductFrames.Construction.CubeProductCoordinates.cubeBundle A b c u hu v hv L)
    (CubeProductFrames.Construction.CubeProductCoordinates.left_frame A b c u hu v hv L sC hsC hC).some
    (CubeProductFrames.Construction.CubeProductCoordinates.right_frame A b c u hu v hv L sB hsB hB).some
    (CubeProductFrames.Construction.CubeProductCoordinates.origin A) (CubeProductFrames.Construction.CubeProductCoordinates.origin_over A) (CubeProductFrames.Construction.CubeProductCoordinates.origin_frame A b c u hu v hv L).some hN

theorem class_eq_one : CubePicardValue.Construction.CubePicardClass.cube A L
    (CubeProductBase.Construction.CubeProductCoordinates.first A b c u hu) (CubeProductBase.Construction.CubeProductCoordinates.second A b c v hv) (CubeProductBase.Construction.CubeProductCoordinates.third A b c) = 1 :=
  CubePicardFaces.Construction.CubePicardClass.eq_one_of_bundle_trivial A L _ _ _ (trivial A b c DB DC u hu v hv sB hsB hB sC hsC hC L)

end Construction.ProjectiveCubeTriviality

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCube
