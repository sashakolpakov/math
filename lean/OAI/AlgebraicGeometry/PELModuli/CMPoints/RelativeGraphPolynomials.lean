import OAI.AlgebraicGeometry.PELModuli.CMPoints.SegreGraphPolynomials
import OAI.AlgebraicGeometry.PELModuli.CMPoints.CoefficientHyperplane
import OAI.AlgebraicGeometry.PELModuli.CMPoints.GraphFieldHilbertPolynomial
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.FieldEmbeddings

/-! # Relative Graph Polynomials -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.RelativeGraphPolynomials

noncomputable section

/-! A specified field-valued morphism has one graph polynomial for every
Segre presentation of its fixed arithmetic source. The resulting Presentations
predicate includes all further field-valued tests. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.FieldEmbeddings.PolarizationEmbedding
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projective_twist_coefficient_transport
    {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {n : ℕ}
    {W Z : Scheme} (f : W ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading k n)) (v : W ⟶ Z)
    (d : Z ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    (h : f ≫ AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n = v ≫ d)
    (j : Fin (n + 1)) (m : ℕ) (L : Z.Modules)
    (e : (Scheme.Modules.pullback d).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m) ≅ L) :
    Nonempty ((Scheme.Modules.pullback f).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := k) j m) ≅
        (Scheme.Modules.pullback v).obj L) := by
  obtain ⟨ec⟩ := CoefficientHyperplane.coefficient_hyperplane_power_iso φ n j m
  let O := SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m
  exact ⟨(Scheme.Modules.pullback f).mapIso ec.symm ≪≫
    (Scheme.Modules.pullbackComp f (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n)).app O ≪≫
    eqToIso (congrArg (fun a => (Scheme.Modules.pullback a).obj O) h) ≪≫
    (Scheme.Modules.pullbackComp v d).symm.app O ≪≫
    (Scheme.Modules.pullback v).mapIso e⟩

theorem exists_relative_morphism_graph_polynomial
    (hPresentations : IntegralModel.Presentations.Hilbert.HilbertHomInput.{0}) {K k : Type} [Field K] [Field k]
    (X : Over (Spec (.of K))) [Flat X.hom] [IsProper X.hom]
    [LocallyOfFinitePresentation X.hom]
    (BX : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X) (t : Spec (.of k) ⟶ Spec (.of K))
    (f : Over.mk t ⨯ X ⟶ X) :
    ∃ Q : Polynomial ℚ, ∀ (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (X ⨯ X)),
      HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation BX BX B →
        HilbertScheme.Presentations.Has.Core.HasFiberHilbertPolynomial B (HilbertScheme.Presentations.HomFunctor.Hom.graphFamily X X f) Q := by
  classical
  obtain ⟨B₀, hB₀, _⟩ := hPresentations X X BX BX 0 (fun i => Fin.elim0 i)
  let I := {B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (X ⨯ X) //
    HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation BX BX B}
  let : Nonempty I := ⟨⟨B₀, hB₀⟩⟩
  let T : Over (Spec (.of K)) := Over.mk t
  let graph := HilbertScheme.Presentations.HomFunctor.Hom.graph X X f
  let dims (B : I) := B.val.dimension
  let F (B : I) := graph.left ≫ IntegralModel.Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding B.val t
  have hclosed (B : I) : IsClosedImmersion (F B) := by
    have := HilbertScheme.Presentations.HomFunctor.Hom.graph_isClosedImmersion X X f
    have := IntegralModel.Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding_closed B.val t
    exact inferInstanceAs (IsClosedImmersion (graph.left ≫ IntegralModel.Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding B.val t))
  let : ∀ B : I, IsClosedImmersion (F B) := hclosed
  let π := (prod.fst : T ⨯ X ⟶ T).left
  have hπ (B : I) : F B ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := k) = π := by
    have hbase : IntegralModel.Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding B.val t ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := k) =
        (prod.fst : T ⨯ (X ⨯ X) ⟶ T).left := IntegralModel.Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding_over B.val t
    rw [Category.assoc, hbase]
    exact congrArg Over.Hom.left (prod.lift_fst _ _)
  let v := graph.left ≫ (prod.snd : T ⨯ (X ⨯ X) ⟶ X ⨯ X).left
  let L (m : ℕ) := (Scheme.Modules.pullback v).obj
    ((SegreGraphPolynomials.segrePresentationLine BX BX).tensorPower m).sheaf
  have hL (B : I) (m : ℕ) : Nonempty ((Scheme.Modules.pullback (F B)).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := k) (0 : Fin (dims B + 1)) m) ≅ L m) := by
    obtain ⟨e⟩ := SegreGraphPolynomials.segrePresentationLine_powers BX BX B.val B.property m
    apply projective_twist_coefficient_transport (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients t).hom
      (F B) v B.val.coefficientEmbedding _ 0 m _ e
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun a => graph.left ≫ a) (IntegralModel.Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding_coefficient B.val t)).trans
        (Category.assoc _ _ _).symm)
  obtain ⟨Q, hQ⟩ := IntegralModel.VaryingProjectiveHilbertPolynomial.PolarizationEmbedding.exists_fixed_varying_e34HilbertPolynomial dims F π hπ (fun _ => 0) L hL
  refine ⟨Q, fun B hB => ?_⟩
  apply GraphFieldHilbertPolynomial.graphFamily_hasFiberHilbertPolynomial_of_field_coordinates X X t B f Q
    (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affineProjectiveChartMap t B.dimension) (F ⟨B, hB⟩)
    (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affineProjectiveChartMap_isPullback t B.dimension)
  · exact (Category.assoc _ _ _).trans
      (congrArg (fun a => graph.left ≫ a) (IntegralModel.Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding_projective B t))
  · exact hπ ⟨B, hB⟩
  · exact hQ ⟨B, hB⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.RelativeGraphPolynomials
