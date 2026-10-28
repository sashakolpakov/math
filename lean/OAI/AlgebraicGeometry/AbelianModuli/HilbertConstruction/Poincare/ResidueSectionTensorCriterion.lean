import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.ZeroFamilyTriviality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.PointSectionTensorFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.Support

/-! # Residue Section Tensor Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Over a one-point parameter scheme, surjectivity of the actual residue-fiber section tensor comparison detects the dual zero section when the residue point is zero. Properness, reducedness, connectedness and a rational point of the fiber follow from the abelian scheme. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S T P : Scheme.{u}} [Subsingleton T] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}
variable (D : Dual.Data.DualAbelianData A) (t : T ⟶ D.abelian.scheme.left)
variable {a : P ⟶ (D.abelian.scheme ⊗ A.scheme).left} {b : P ⟶ T}
variable (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.scheme.hom) t)

include H in
theorem Dual.Data.DualAbelianData.poincareBaseFamily_zero_of_residue_section_tensor
    (x : T)
    (hpoint : T.fromSpecResidueField x ≫ t =
      ((T.fromSpecResidueField x ≫ t) ≫ D.abelian.scheme.hom) ≫ η[D.abelian.scheme].left)
    (hsurj : Function.Surjective
      ((Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison (IsPullback.of_hasPullback b (T.fromSpecResidueField x))
        (D.poincare.pullback a).sheaf).app (op ⊤))) :
    t = (t ≫ D.abelian.scheme.hom) ≫ η[D.abelian.scheme].left := by
  let p := pullback.fst D.abelian.scheme.hom A.scheme.hom
  let r := T.fromSpecResidueField x
  have hAproper : IsProper A.scheme.hom := A.proper
  have hAsmooth : Smooth A.scheme.hom := inferInstance
  have hAconnected : GeometricallyConnected A.scheme.hom := A.connected
  have : IsProper p := MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback D.abelian.scheme.hom A.scheme.hom).flip hAproper
  have : Smooth p := MorphismProperty.of_isPullback (P := @Smooth)
    (IsPullback.of_hasPullback D.abelian.scheme.hom A.scheme.hom).flip hAsmooth
  have : GeometricallyConnected p := MorphismProperty.of_isPullback (P := @GeometricallyConnected)
    (IsPullback.of_hasPullback D.abelian.scheme.hom A.scheme.hom).flip hAconnected
  have : IsProper b := MorphismProperty.of_isPullback (P := @IsProper) H inferInstance
  have : Smooth b := MorphismProperty.of_isPullback (P := @Smooth) H inferInstance
  have : GeometricallyConnected b :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) H inferInstance
  have : IsProper (b.fiberToSpecResidueField x) :=
    inferInstanceAs (IsProper (pullback.snd b r))
  have hFiberSmooth : Smooth (b.fiberToSpecResidueField x) :=
    MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback b r)
      (show Smooth b from inferInstance)
  have : GeometricallyConnected (b.fiberToSpecResidueField x) :=
    inferInstanceAs (GeometricallyConnected (pullback.snd b r))
  have : IsReduced (b.fiber x) :=
    @HilbertConstruction.Smooth.ReducedFibers.smoothOverField_isReduced (T.residueField x) inferInstance (b.fiber x)
      (b.fiberToSpecResidueField x) hFiberSmooth
  have : ConnectedSpace (b.fiber x) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (b.fiberToSpecResidueField x)
  have hzA : η[A.scheme].left ≫ A.scheme.hom = 𝟙 S := η[A.scheme].w
  let v : T ⟶ A.scheme.left := (t ≫ D.abelian.scheme.hom) ≫ η[A.scheme].left
  have hv : t ≫ D.abelian.scheme.hom = v ≫ A.scheme.hom := by
    change _ = ((t ≫ D.abelian.scheme.hom) ≫ η[A.scheme].left) ≫ A.scheme.hom
    rw [Category.assoc, hzA, Category.comp_id]
  let σ : T ⟶ (D.abelian.scheme ⊗ A.scheme).left := pullback.lift t v hv
  have hσ : σ ≫ p = (𝟙 T) ≫ t :=
    (pullback.lift_fst t v hv).trans (Category.id_comp t).symm
  let s : T ⟶ P := H.lift σ (𝟙 T) hσ
  have hs : s ≫ b = 𝟙 T := H.lift_snd σ (𝟙 T) hσ
  have hsr : (r ≫ s) ≫ b = (𝟙 (Spec (T.residueField x))) ≫ r := by
    rw [Category.assoc, hs, Category.comp_id, Category.id_comp]
  let y : Spec (T.residueField x) ⟶ b.fiber x := pullback.lift (r ≫ s) (𝟙 _) hsr
  have hy : y ≫ b.fiberToSpecResidueField x = 𝟙 _ := pullback.lift_snd _ _ _
  let HF : IsPullback (b.fiberι x ≫ a) (b.fiberToSpecResidueField x) p (r ≫ t) :=
    (IsPullback.of_hasPullback b r).paste_horiz H
  obtain ⟨ef⟩ := D.poincareBaseFamily_zero_implies_trivial (r ≫ t) HF hpoint
  let L := D.poincare.pullback a
  let e : (L.pullback (b.fiberι x)).sheaf ≅ Line.Bundles.structureModule (b.fiber x) :=
    (Scheme.Modules.pullbackComp (b.fiberι x) a).app D.poincare.sheaf ≪≫ ef
  exact D.poincareBaseFamily_trivial_implies_zero t H
    (Single.PointSectionTensorFrames.lineBundle_trivial_of_single_fiber_section_tensor b x L e y hy hsurj)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
