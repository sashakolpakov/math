import OAI.AlgebraicGeometry.SheafCohomology.Projective.ScalarBundle
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmpleEmbeddingPower
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Projectivity
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.LineBundleInvariance

/-! # Symmetric Projective Embedding -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SymmetricProjectiveEmbedding

noncomputable section

/-! A genuine projective embedding whose hyperplane bundle is symmetric,
constructed from the ample symmetric bundle of an abelian variety. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.SheafCohomology.Projective.ScalarBundle
attribute [local instance] MvPolynomial.gradedAlgebra

theorem ample_exists_field_closed_embedding_power
    {K : Type} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : L.IsAmple) :
    ∃ d : ℕ, 0 < d ∧ ∃ (n : ℕ)
      (a : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)),
      IsClosedImmersion a ∧ a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = f ∧
        Nonempty ((Scheme.Modules.pullback a).obj
          (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := K) (0 : Fin (n + 1))).sheaf ≅
            (L.tensorPower d).sheaf) := by
  obtain ⟨d, hd, n, a, ha, hb, ⟨eL⟩⟩ := ArithmeticGeometry.OrdinaryLocus.Openness.AmpleEmbeddingPower.Construction.ample_exists_closed_embedding_power f L hL
  let S := Spec (CommRingCat.of K)
  let R := Γ(S, ⊤)
  let e : K ≃+* R := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  let π := AlgebraicGeometry.SheafCohomology.Projective.ScalarBundle.projectiveScalarIso e n
  let a' : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) := a ≫ π.hom
  have : IsClosedImmersion a := ha
  have hbase : S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (R := K) (S := R) e.toRingHom) = 𝟙 S := by
    have he : Spec.map (CommRingCat.ofHom (R := K) (S := R) e.toRingHom) = S.isoSpec.inv :=
      (Scheme.isoSpec_Spec_inv (CommRingCat.of K)).symm
    rw [he]
    exact S.isoSpec.hom_inv_id
  have hπ : π.hom ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) =
      AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) ≫ Spec.map (CommRingCat.ofHom (R := K) (S := R) e.toRingHom) :=
    AlgebraicGeometry.SheafCohomology.Projective.ScalarBundle.projectiveScalarMap_over e.toRingHom n
  refine ⟨d, hd, n, a', inferInstance, ?_, ⟨?_⟩⟩
  · change (a ≫ π.hom) ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = f
    rw [Category.assoc, hπ, ← Category.assoc, hb, Category.assoc, hbase, Category.comp_id]
  · exact (Scheme.Modules.pullbackComp a π.hom).symm.app _ ≪≫
      (Scheme.Modules.pullback a).mapIso (AlgebraicGeometry.SheafCohomology.Projective.ScalarBundle.projectiveScalarMap_bundleIso e.toRingHom n 0 0) ≪≫ eL

theorem exists_symmetric_projective_embedding
    {K : Type} [Field K] [IsAlgClosed K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom] :
    ∃ (n : ℕ) (a : A.left ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)),
      IsClosedImmersion a ∧ a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = A.hom ∧
      Nonempty ((((AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := K) (0 : Fin (n + 1))).pullback a).pullback
        (GrpObj.inv (X := A)).left).sheaf ≅
          ((AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := K) (0 : Fin (n + 1))).pullback a).sheaf) := by
  obtain ⟨L, hL, hsym⟩ := AlgebraicGeometry.FormalGeometry.Completion.Geometric.Projectivity.Construction.exists_symmetric_ample_lineBundle A
  obtain ⟨d, _, n, a, ha, hbase, ⟨e⟩⟩ := ample_exists_field_closed_embedding_power A.hom L hL
  have hs := AlgebraicGeometry.FormalGeometry.Completion.Geometric.LineBundleInvariance.Construction.symmetric_lineBundle_tensorPower K A L hsym d
  exact ⟨n, a, ha, hbase, ⟨(Scheme.Modules.pullback (GrpObj.inv (X := A)).left).mapIso e ≪≫
    hs.some ≪≫ e.symm⟩⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SymmetricProjectiveEmbedding
