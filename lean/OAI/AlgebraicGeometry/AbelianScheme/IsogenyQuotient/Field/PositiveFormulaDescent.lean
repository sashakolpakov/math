import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RecoveredPicardInjection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PositiveLineOn
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PicardSquareComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeometricAmpleNeighborhood

/-! # Positive Formula Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PositiveFormulaDescent.Construction

noncomputable section

/-! An actual recovered ample line and its Poincare tensor formula
give the full positive line formula over the original ground field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false in
theorem positiveLineFormula_of_recovered_field_witness
    {k K : Type} [Field k] [Field K]
    (u : Spec (.of K) ⟶ Spec (.of k))
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K)))
    (e : B.scheme ≅ (A.pullback u).scheme) [IsMonHom e.hom]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) (J : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.scheme.left)
    (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A.scheme ⊗ A.scheme).left) (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (B.scheme ⊗ B.scheme).left)
    (hL : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap u B.scheme A.scheme e)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J)
    (hQ : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.tensorMap u B.scheme A.scheme e)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P)
    (hJ : J.IsAmple)
    (hm : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P * Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst B.scheme B.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J) *
        Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (snd B.scheme B.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J) =
          Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback μ[B.scheme].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf J)) :
    AbelianModuli.ReferenceFamily.PositiveLineOn.PositiveLineFormula A Q := by
  have : Surjective u := ⟨Function.surjective_to_subsingleton _⟩
  let c := AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap u B.scheme A.scheme e
  let q := AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.tensorMap u B.scheme A.scheme e
  have hample : L.IsAmple := PELModuli.IntegralModel.GeometricAmpleNeighborhood.proper_isAmple_of_field_baseChange A.scheme.hom L
    c B.scheme.hom u (AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap_isPullback u B.scheme A.scheme e).flip
    (hJ.of_iso (Quotient.exact hL).some.symm)
  have : Subsingleton (𝟙_ (Over (Spec (.of k)))).left := inferInstanceAs (Subsingleton (Spec (.of k)))
  have : Nonempty (𝟙_ (Over (Spec (.of k)))).left := inferInstanceAs (Nonempty (Spec (.of k)))
  apply (AbelianModuli.ReferenceFamily.PositiveLineOn.positiveLineFormula_iff_class A Q).mpr
  refine ⟨L, hample, Quotient.sound (L.pullback η[A.scheme].left).exists_trivialization_of_subsingleton, ?_⟩
  apply RecoveredPicardInjection.Construction.recovered_field_product_picard_pullback_injective u A B.scheme e A B.scheme e
  change Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback q
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q * Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst A.scheme A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
      Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (snd A.scheme A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) =
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback q (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback μ[A.scheme].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))
  have h₁ := AbelianModuli.ReferenceFamily.PicardSquareComparison.picardPullback_square q (fst A.scheme A.scheme).left
    (fst B.scheme B.scheme).left c (AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.tensorMap_fst u B.scheme A.scheme e)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)
  have h₂ := AbelianModuli.ReferenceFamily.PicardSquareComparison.picardPullback_square q (snd A.scheme A.scheme).left
    (snd B.scheme B.scheme).left c (AbelianModuli.ReferenceFamily.CartesianFiberComparison.CartesianFamily.tensorMap_snd u B.scheme A.scheme e)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)
  have h₃ := AbelianModuli.ReferenceFamily.PicardSquareComparison.picardPullback_square q μ[A.scheme].left μ[B.scheme].left c
    (RecoveredPicardInjection.Construction.recovered_product_multiplication u A B.scheme e) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)
  rw [map_mul, map_mul, hQ, h₁, h₂, h₃, hL]
  exact hm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PositiveFormulaDescent.Construction
