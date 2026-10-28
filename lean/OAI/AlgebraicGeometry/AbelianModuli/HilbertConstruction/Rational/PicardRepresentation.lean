import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PicardComparison
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.NormalizedRigidifiedFamily
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.NoetherianHomogeneousLineModel
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReferenceAffineTestCoordinates
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.HomogeneousBaseChangeForgetting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.UniversalGlobalFunctions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.PicardInclusionFaithfulness
import OAI.RepresentationTheory.Theta.Geometric.Affine.CoverLocalSurjectivity
import OAI.RepresentationTheory.Theta.Geometric.HomogeneousParameterEmbedding
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Picard Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PicardRepresentation

noncomputable section

/-! An injective homogeneous family with every geometric homogeneous
class represents the original homogeneous Picard sheaf over a
Noetherian rational affine base. Noetherian approximation of the actual
line family extends the comparison theorem to all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable {R : Type} [CommRing R] [hR : IsNoetherianRing R] {g : ℕ}
    (qS : Spec (.of R) ⟶ Spec (.of ℚ))
    (A B : Abelian.Schemes.AbelianScheme g (Spec (.of R)))
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A.scheme B.scheme)
    (hD : A.IsHomogeneousPicardClass B.scheme (Line.Bundles.LineBundle.classOf D.bundle))
    (hinj : ∀ V : Over (Spec (.of R)), Function.Injective (D.relativeValue (T := V)))
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k] (f : Spec (.of k) ⟶ Spec (.of R))
      (x : A.homogeneousPicardSheaf.obj.obj
        (.op ((Over.map f).obj (Over.mk (𝟙 (Spec (.of k))))))),
      ∃ a : (Over.map f).obj (Over.mk (𝟙 (Spec (.of k)))) ⟶ B.scheme,
        D.relativeValue a = A.homogeneousPicardSheafInclusion.hom.app
          (.op ((Over.map f).obj (Over.mk (𝟙 (Spec (.of k)))))) x)

include hR qS P hinj hgeom

omit hR in
theorem rational_noetherian_homogeneous_class_has_parameter
    (U : Over (Spec (.of R))) [IsLocallyNoetherian U.left]
    (q : A.homogeneousPicardPresheaf.obj (.op U)) :
    ∃ a : U ⟶ B.scheme,
      (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap A D.bundle hD).app (.op U) (ULift.up a) =
        (toSheafify (Scheme.fppfTopology.over (Spec (.of R)))
          A.homogeneousPicardPresheaf).app (.op U) q := by
  let L := q.val.out
  have hc : Line.Bundles.LineBundle.classOf L = q.val := Quotient.out_eq _
  have hL : A.IsHomogeneousPicardClass U (Line.Bundles.LineBundle.classOf L) := hc.symm ▸ q.property
  let C := Picard.ThetaConstruction.NormalizedRigidifiedFamily.Geometric.normalizedRigidifiedFamily A U L
  have hC := Picard.ThetaConstruction.NormalizedRigidifiedFamily.Geometric.normalizedRigidifiedFamily_homogeneous A U L hL
  obtain ⟨a, ha, _⟩ := PicardComparison.rationalPicard_existsUnique_parameter qS A B P D hinj C hgeom hC
  refine ⟨a, ?_⟩
  apply A.homogeneousPicardSectionInclusion_injective U
  exact (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_forget A D.bundle hD a).trans
    (ha.trans ((Picard.ThetaConstruction.NormalizedRigidifiedFamily.Geometric.normalizedRigidifiedFamily_value_id A U L).trans
      ((congrArg ((Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)) hc).trans
        (Picard.ThetaConstruction.HomogeneousBaseChangeForgetting.Geometric.homogeneousForget_toSheafify A U q).symm)))

theorem rational_algebra_homogeneous_class_has_parameter
    {K : Type} [CommRing K] [Algebra R K]
    (q : A.homogeneousPicardPresheaf.obj (.op (ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver R K))) :
    ∃ a : ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver R K ⟶ B.scheme,
      (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap A D.bundle hD).app _ (ULift.up a) =
        (toSheafify (Scheme.fppfTopology.over (Spec (.of R)))
          A.homogeneousPicardPresheaf).app _ q := by
  let U := ReferenceFamily.Finite.CoefficientLimit.algebraSpecOver R K
  let L : Line.Bundles.LineBundle (U ⊗ A.scheme).left := q.val.out
  have hc : Line.Bundles.LineBundle.classOf L = q.val := Quotient.out_eq _
  have hL : A.IsHomogeneousPicardClass U (Line.Bundles.LineBundle.classOf L) := hc.symm ▸ q.property
  have hΓ := Picard.ThetaConstruction.RelativeTriviality.Geometric.projectiveFamily_hasUniversalGlobalFunctions P
  obtain ⟨V, hV, M, j, hM, hclass⟩ := Picard.ThetaConstruction.NoetherianHomogeneousLineModel.Geometric.exists_noetherian_homogeneous_line_model A hΓ L hL
  let : IsLocallyNoetherian V.left := hV
  let qM : A.homogeneousPicardPresheaf.obj (.op V) := ⟨Line.Bundles.LineBundle.classOf M, hM⟩
  obtain ⟨a, ha⟩ := rational_noetherian_homogeneous_class_has_parameter
    qS A B P D hD hinj hgeom V qM
  have hq : A.homogeneousPicardPresheaf.map j.op qM = q := by
    apply Subtype.ext
    exact hclass.trans hc
  let sheafifyMap := toSheafify (Scheme.fppfTopology.over (Spec (.of R)))
    A.homogeneousPicardPresheaf
  refine ⟨j ≫ a, (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_naturality A D.bundle hD a j).symm.trans ?_⟩
  exact (congrArg (A.homogeneousPicardSheaf.obj.map j.op) ha).trans
    ((sheafifyMap.naturality_apply j.op qM).symm.trans
      (congrArg (sheafifyMap.app (.op U)) hq))

theorem rationalHomogeneousParameterMap_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of R)))
      (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap A D.bundle hD) := by
  let HP := A.homogeneousPicardPresheaf
  let G := A.homogeneousPicardSheaf.obj
  let sheafifyMap := toSheafify (Scheme.fppfTopology.over (Spec (.of R))) HP
  let : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of R))) sheafifyMap :=
    inferInstanceAs (Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of R)))
      (toSheafify (Scheme.fppfTopology.over (Spec (.of R))) A.homogeneousPicardPresheaf))
  refine @RepresentationTheory.Theta.Geometric.Affine.CoverLocalSurjectivity.locallySurjective_of_affine_representatives (Spec (.of R))
    (uliftYoneda.{1}.obj B.scheme) HP G
    (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap A D.bundle hD) sheafifyMap this ?_
  intro U _ q
  let := Picard.ThetaConstruction.ReferenceAffineTestCoordinates.Geometric.originalAffineGroundAlgebra R U
  let e := Picard.ThetaConstruction.ReferenceAffineTestCoordinates.Geometric.originalAffineTestIso R U
  let q' := HP.map e.inv.op q
  obtain ⟨a, ha⟩ := rational_algebra_homogeneous_class_has_parameter
    qS A B P D hD hinj hgeom q'
  have hq : HP.map e.hom.op q' = q := by
    change HP.map e.hom.op (HP.map e.inv.op q) = q
    rw [← Functor.map_comp_apply, ← op_comp, e.hom_inv_id, op_id, Functor.map_id_apply]
  refine ⟨ULift.up (e.hom ≫ a),
    (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_naturality A D.bundle hD a e.hom).symm.trans ?_⟩
  exact (congrArg (G.map e.hom.op) ha).trans
    ((sheafifyMap.naturality_apply e.hom.op q').symm.trans
      (congrArg (sheafifyMap.app (.op U)) hq))

theorem rationalHomogeneousParameterMap_isIso :
    IsIso (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap A D.bundle hD) := by
  let J := Scheme.fppfTopology.over (Spec (.of R))
  let f : J.uliftYoneda.{1}.obj B.scheme ⟶ A.homogeneousPicardSheaf :=
    ⟨RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap A D.bundle hD⟩
  have hm : Mono f.hom := RepresentationTheory.Theta.Geometric.HomogeneousParameterEmbedding.homogeneousParameterMap_mono A D.bundle hD hinj
  let : Mono f := (sheafToPresheaf _ _).mono_of_mono_map hm
  let : Presheaf.IsLocallySurjective J f.hom :=
    rationalHomogeneousParameterMap_locallySurjective qS A B P D hD hinj hgeom
  let : IsIso f := isIso_of_mono_of_epi f
  exact inferInstanceAs (IsIso ((sheafToPresheaf _ _).map f))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PicardRepresentation
