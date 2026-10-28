import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineNeighborhoodTrivial
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductFrames
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupIrreducibleOf
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeSmooth

/-! # Cube Product Lift -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CubeProductLift

noncomputable section

section

/-! The actual cube line bundle becomes trivial after replacing its first
 two factors by pointed projective modifications. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductFrames.Construction.CubeProductCoordinates

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  {B C : Scheme} (b : B ⟶ Spec (.of K)) (c : C ⟶ Spec (.of K))
  [IsProper b] [IsProper c] [GeometricallyIntegral b] [GeometricallyIntegral c]
  (DB : Quotients.FiniteDescent.AffineSectionOf.Construction.AffineSectionCover.Data B) (DC : Quotients.FiniteDescent.AffineSectionOf.Construction.AffineSectionCover.Data C)
  (u : B ⟶ A.left) (hu : u ≫ A.hom = b) (v : C ⟶ A.left) (hv : v ≫ A.hom = c)
  (sb : Spec (.of K) ⟶ B) (hsb : sb ≫ b = 𝟙 _) (hub : sb ≫ u = Quotients.FiniteDescent.CubeProductFrames.Construction.CubeProductCoordinates.origin A)
  (sc : Spec (.of K) ⟶ C) (hsc : sc ≫ c = 𝟙 _) (hvc : sc ≫ v = Quotients.FiniteDescent.CubeProductFrames.Construction.CubeProductCoordinates.origin A)

include DB DC hsb hsc hub hvc

theorem modifiedCube_trivial (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) :
    Nonempty ((Quotients.FiniteDescent.CubeProductFrames.Construction.CubeProductCoordinates.cubeBundle A b c u hu v hv L).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.total A b c)) := by
  classical
  have : IsReduced A.left := Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.reduced_of_smooth_field A.hom
  have : IrreducibleSpace A.left := Quotients.FiniteDescent.GroupIrreducibleOf.Construction.GroupIrreducible.irreducibleSpace_of_connected_group A
  have : IsIntegral A.left := isIntegral_of_irreducibleSpace_of_isReduced A.left
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  let eb := (Fintype.equivFin DB.I).symm
  let ec := (Fintype.equivFin DC.I).symm
  let U : Fin (Fintype.card DB.I) → B.Opens := fun i => AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (DB.sectionHom (eb i))
  let V : Fin (Fintype.card DC.I) → C.Opens := fun i => AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (DC.sectionHom (ec i))
  have hcU : iSup U = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := DB.covers x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨eb.symm i, by simpa only [U, eb.apply_symm_apply] using hi⟩
  have hcV : iSup V = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := DC.covers x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨ec.symm i, by simpa only [V, ec.apply_symm_apply] using hi⟩
  obtain ⟨ib, hib⟩ := DB.covers (sb (IsLocalRing.closedPoint K))
  obtain ⟨ic, hic⟩ := DC.covers (sc (IsLocalRing.closedPoint K))
  have hbi : ⊤ ≤ Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.familyPoint A b sb hsb ⁻¹ᵁ
      (pullback.fst b A.hom ⁻¹ᵁ U (eb.symm ib)) := by
    intro x _
    change (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.familyPoint A b sb hsb ≫ pullback.fst b A.hom) x ∈ U (eb.symm ib)
    rw [Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.familyPoint, pullback.lift_fst]
    change sb (A.hom x) ∈ U (eb.symm ib)
    rw [Subsingleton.elim (A.hom x) (IsLocalRing.closedPoint K)]
    simpa only [U, eb.apply_symm_apply] using hib
  have hci : ⊤ ≤ Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.familyPoint A c sc hsc ⁻¹ᵁ
      (pullback.fst c A.hom ⁻¹ᵁ V (ec.symm ic)) := by
    intro x _
    change (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.familyPoint A c sc hsc ≫ pullback.fst c A.hom) x ∈ V (ec.symm ic)
    rw [Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.familyPoint, pullback.lift_fst]
    change sc (A.hom x) ∈ V (ec.symm ic)
    rw [Subsingleton.elim (A.hom x) (IsLocalRing.closedPoint K)]
    simpa only [V, ec.apply_symm_apply] using hic
  obtain ⟨ex⟩ := Quotients.FiniteDescent.CubeProductFrames.Construction.CubeProductCoordinates.left_frame A b c u hu v hv L sc hsc hvc
  obtain ⟨ey⟩ := Quotients.FiniteDescent.CubeProductFrames.Construction.CubeProductCoordinates.right_frame A b c u hu v hv L sb hsb hub
  obtain ⟨ez⟩ := Quotients.FiniteDescent.CubeProductFrames.Construction.CubeProductCoordinates.origin_frame A b c u hu v hv L
  apply Quotients.FiniteDescent.AffineNeighborhoodTrivial.Construction.AffineNeighborhoodSeesaw.trivial b c DB DC
    (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) (pullback.fst b A.hom) (pullback.fst c A.hom)
    A.hom (IsPullback.of_hasPullback b A.hom) (IsPullback.of_hasPullback c A.hom)
    U V (fun i => DB.affine (eb i)) (fun i => DC.affine (ec i)) hcU hcV
    (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.familyPoint A b sb hsb) (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.familyPoint_over A b sb hsb)
    (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.familyPoint A c sc hsc) (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.familyPoint_over A c sc hsc)
    (eb.symm ib) hbi (ec.symm ic) hci (Quotients.FiniteDescent.CubeProductFrames.Construction.CubeProductCoordinates.cubeBundle A b c u hu v hv L) ex ey
    (Quotients.FiniteDescent.CubeProductFrames.Construction.CubeProductCoordinates.origin A) (Quotients.FiniteDescent.CubeProductFrames.Construction.CubeProductCoordinates.origin_over A) ez
  intro x
  obtain ⟨W, hW, hpoints⟩ := Quotients.FiniteDescent.GroupIrreducibleOf.Construction.GroupIrreducible.exists_affineOpen_of_finite A
    {x, Quotients.FiniteDescent.RationalPoint.Construction.RationalPointResidue.point (Quotients.FiniteDescent.CubeProductFrames.Construction.CubeProductCoordinates.origin A)} (Set.toFinite _)
  exact ⟨W, hW, hpoints (by simp), hpoints (by simp)⟩

end

/-! Pulling the modified cube identity back along its actual three
coordinate maps. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductFrames.Construction.CubeProductCoordinates

variable {K : Type} [Field K]
  (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
  {B C : Scheme} (b : B ⟶ Spec (.of K)) (c : C ⟶ Spec (.of K))
  {T : Over (Spec (.of K))}

omit [GrpObj A] [IsCommMonObj A] in
def cubeProductLift (f : T ⟶ Over.mk b) (g : T ⟶ Over.mk c) (h : T ⟶ A) :
    T ⟶ Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.ambient A b c :=
  Over.homMk
    (pullback.lift (pullback.lift f.left h.left (f.w.trans h.w.symm))
      (pullback.lift g.left h.left (g.w.trans h.w.symm)) (by
        simp only [Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.leftBase, Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.rightBase, pullback.lift_snd])) (by
    change (_ ≫ pullback.fst (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) ≫ Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) ≫ A.hom = _
    simp only [pullback.lift_fst_assoc, Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.leftBase, pullback.lift_snd]
    exact h.w)

omit [GrpObj A] [IsCommMonObj A] in
theorem cubeProductLift_first (f : T ⟶ Over.mk b) (g : T ⟶ Over.mk c) (h : T ⟶ A)
    (u : B ⟶ A.left) (hu : u ≫ A.hom = b) :
    cubeProductLift A b c f g h ≫ Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.first A b c u hu = f ≫ Over.homMk u hu := by
  apply Over.OverMorphism.ext
  change _ ≫ (pullback.fst (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) ≫ pullback.fst b A.hom ≫ u) = _
  simp only [cubeProductLift, Over.homMk_left, pullback.lift_fst_assoc]
  rfl

omit [GrpObj A] [IsCommMonObj A] in
theorem cubeProductLift_second (f : T ⟶ Over.mk b) (g : T ⟶ Over.mk c) (h : T ⟶ A)
    (v : C ⟶ A.left) (hv : v ≫ A.hom = c) :
    cubeProductLift A b c f g h ≫ Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.second A b c v hv = g ≫ Over.homMk v hv := by
  apply Over.OverMorphism.ext
  change _ ≫ (pullback.snd (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) ≫ pullback.fst c A.hom ≫ v) = _
  simp only [cubeProductLift, Over.homMk_left, pullback.lift_snd_assoc, pullback.lift_fst_assoc]
  rfl

omit [GrpObj A] [IsCommMonObj A] in
theorem cubeProductLift_third (f : T ⟶ Over.mk b) (g : T ⟶ Over.mk c) (h : T ⟶ A) :
    cubeProductLift A b c f g h ≫ Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.third A b c = h := by
  apply Over.OverMorphism.ext
  change _ ≫ (pullback.fst (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.leftBase A b) (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.rightBase A c) ≫ pullback.snd b A.hom) = _
  simp only [cubeProductLift, Over.homMk_left, pullback.lift_fst_assoc, pullback.lift_snd]

omit [IsCommMonObj A] in
theorem cube_eq_one_of_modifiedCube_trivial
    (u : B ⟶ A.left) (hu : u ≫ A.hom = b) (v : C ⟶ A.left) (hv : v ≫ A.hom = c)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (he : Nonempty ((Quotients.FiniteDescent.CubeProductFrames.Construction.CubeProductCoordinates.cubeBundle A b c u hu v hv L).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.total A b c)))
    (f : T ⟶ Over.mk b) (g : T ⟶ Over.mk c) (h : T ⟶ A) :
    Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.cube A L (f ≫ Over.homMk u hu) (g ≫ Over.homMk v hv) h = 1 := by
  have hz := Quotients.FiniteDescent.CubePicardFaces.Construction.CubePicardClass.eq_one_of_bundle_trivial A L
    (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.first A b c u hu) (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.second A b c v hv) (Quotients.FiniteDescent.CubeProductBase.Construction.CubeProductCoordinates.third A b c) he
  have hp := congrArg (Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map (cubeProductLift A b c f g h).left) hz
  rw [Quotients.FiniteDescent.CubePicardValue.Construction.CubePicardClass.pullback, map_one, cubeProductLift_first,
    cubeProductLift_second, cubeProductLift_third] at hp
  exact hp

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CubeProductLift
