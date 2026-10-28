import OAI.AlgebraicGeometry.SheafCohomology.Projective.ScalarBundle
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexBase
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmpleEmbeddingPower

/-! # Ample Complex Embedding -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.AmpleComplexEmbedding

noncomputable section

/-! A positive power of an actual ample bundle is the pullback of the
hyperplane bundle from a closed embedding into native complex projective space. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ample_exists_complex_closed_embedding_power {X : Scheme}
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [IsProper f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : L.IsAmple) :
    ∃ d : ℕ, 0 < d ∧ ∃ (n : ℕ) (a : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n),
      IsClosedImmersion a ∧ a ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n = f ∧
        Nonempty ((Scheme.Modules.pullback a).obj
          (Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := ℂ) (0 : Fin (n + 1))).sheaf ≅
            (L.tensorPower d).sheaf) := by
  obtain ⟨d, hd, n, a, ha, hb, ⟨eL⟩⟩ := ArithmeticGeometry.OrdinaryLocus.Openness.AmpleEmbeddingPower.Construction.ample_exists_closed_embedding_power f L hL
  let R := Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)
  let e : ℂ ≃+* R := (Scheme.ΓSpecIso (.of ℂ)).symm.commRingCatIsoToRingEquiv
  let π := ScalarBundle.projectiveScalarIso e n
  let a' : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n := a ≫ π.hom
  have : IsClosedImmersion a := ha
  have hbase : Foundations.Scheme.ProjectiveSpace.complexBase.toSpecΓ ≫ Spec.map (CommRingCat.ofHom e.toRingHom) = 𝟙 Foundations.Scheme.ProjectiveSpace.complexBase := by
    have he : Spec.map (CommRingCat.ofHom e.toRingHom) = Foundations.Scheme.ProjectiveSpace.complexBase.isoSpec.inv :=
      (Scheme.isoSpec_Spec_inv (.of ℂ)).symm
    rw [he]
    exact Foundations.Scheme.ProjectiveSpace.complexBase.isoSpec.hom_inv_id
  have hπ : π.hom ≫ MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := ℂ) =
      MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) ≫ Spec.map (CommRingCat.ofHom e.toRingHom) :=
    ScalarBundle.projectiveScalarMap_over e.toRingHom n
  refine ⟨d, hd, n, a', inferInstance, ?_, ⟨?_⟩⟩
  · change (a ≫ π.hom) ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n = f
    rw [ComplexBase.projectiveSpaceToBase_eq_homogeneousProjπ, Category.assoc,
      hπ, ← Category.assoc, hb, Category.assoc, hbase, Category.comp_id]
  · exact (Scheme.Modules.pullbackComp a π.hom).symm.app _ ≪≫
      (Scheme.Modules.pullback a).mapIso (ScalarBundle.projectiveScalarMap_bundleIso e.toRingHom n 0 0) ≪≫ eL

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.AmpleComplexEmbedding
