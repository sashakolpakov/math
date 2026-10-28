import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SegreHyperplaneComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.HyperplanePullbackPowers
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.VaryingProjectiveHilbertPolynomial
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Coefficient
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.GraphPolarizationPowers

/-! # Segre Graph Polynomials -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.SegreGraphPolynomials

noncomputable section

/-! The graph polynomial of a specified morphism is independent of the
Segre presentation subsequently chosen by the full Presentations input. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

def segrePresentationLine {S : Scheme.{0}} {X Y : Over S}
    (BX : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X)
    (BY : HilbertScheme.Presentations.Has.Core.ProjectivePresentation Y) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (X ⨯ Y).left :=
  ((IntegralModel.Projective.HyperplanePowers.PolarizationEmbedding.projectiveHyperplaneLine Γ(S, ⊤) BX.dimension 0).pullback
    ((prod.fst : X ⨯ Y ⟶ X).left ≫ BX.coefficientEmbedding)).tensor
      ((IntegralModel.Projective.HyperplanePowers.PolarizationEmbedding.projectiveHyperplaneLine Γ(S, ⊤) BY.dimension 0).pullback
        ((prod.snd : X ⨯ Y ⟶ Y).left ≫ BY.coefficientEmbedding))

theorem segrePresentationLine_powers {S : Scheme.{0}} {X Y : Over S}
    (BX : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X)
    (BY : HilbertScheme.Presentations.Has.Core.ProjectivePresentation Y)
    (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (X ⨯ Y))
    (hB : HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation BX BY B) (m : ℕ) :
    Nonempty ((Scheme.Modules.pullback B.coefficientEmbedding).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := Γ(S, ⊤))
        (0 : Fin (B.dimension + 1)) m) ≅ ((segrePresentationLine BX BY).tensorPower m).sheaf) :=
  IntegralModel.HyperplanePullbackPowers.PolarizationEmbedding.hyperplane_pullback_power_iso B.coefficientEmbedding (segrePresentationLine BX BY) 0
    (IntegralModel.SegreHyperplaneComparison.PolarizationEmbedding.exists_segre_hyperplane_iso BX BY B hB 0 0 0) m

theorem exists_fixed_morphism_graph_polynomial
    (hPresentations : IntegralModel.Presentations.Hilbert.HilbertHomInput.{0}) {k : Type} [Field k]
    (X : Over (Spec (.of k))) [Flat X.hom] [IsProper X.hom]
    [LocallyOfFinitePresentation X.hom]
    (BX : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X) (f : X ⟶ X) :
    ∃ Q : Polynomial ℚ,
      ∀ (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (X ⨯ X)),
        HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation BX BX B →
        HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
          (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf ((IntegralModel.Presentations.GraphPolarizationPowers.PolarizationEmbedding.e34Graph X f).left ≫ B.coefficientEmbedding).ker).toIdeal Q := by
  classical
  have hR : IsField Γ(Spec (.of k), ⊤) :=
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField k)
  let := hR.toField
  obtain ⟨B₀, hB₀, _⟩ := hPresentations X X BX BX 0 (fun i => Fin.elim0 i)
  let I := {B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (X ⨯ X) //
    HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation BX BX B}
  let : Nonempty I := ⟨⟨B₀, hB₀⟩⟩
  let dims (B : I) := B.val.dimension
  let F (B : I) := (IntegralModel.Presentations.GraphPolarizationPowers.PolarizationEmbedding.e34Graph X f).left ≫ B.val.coefficientEmbedding
  have hclosed (B : I) : IsClosedImmersion (F B) := by
    have := IntegralModel.Presentations.GraphPolarizationPowers.PolarizationEmbedding.e34Graph_closed X f
    have := IntegralModel.Presentations.Coefficient.PolarizationEmbedding.e34CoefficientEmbedding_closed B.val
    dsimp only [F]
    infer_instance
  let : ∀ B : I, IsClosedImmersion (F B) := hclosed
  let π := X.hom ≫ (Spec (.of k)).toSpecΓ
  have hπ (B : I) : F B ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := Γ(Spec (.of k), ⊤)) = π := by
    change ((IntegralModel.Presentations.GraphPolarizationPowers.PolarizationEmbedding.e34Graph X f).left ≫ B.val.coefficientEmbedding) ≫ _ = _
    rw [Category.assoc, IntegralModel.Presentations.Coefficient.PolarizationEmbedding.e34CoefficientEmbedding_over, ← Category.assoc, (IntegralModel.Presentations.GraphPolarizationPowers.PolarizationEmbedding.e34Graph X f).w]
  let L (m : ℕ) := (Scheme.Modules.pullback (IntegralModel.Presentations.GraphPolarizationPowers.PolarizationEmbedding.e34Graph X f).left).obj
    ((segrePresentationLine BX BX).tensorPower m).sheaf
  have hL (B : I) (m : ℕ) : Nonempty ((Scheme.Modules.pullback (F B)).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := Γ(Spec (.of k), ⊤))
        (0 : Fin (dims B + 1)) m) ≅ L m) := by
    obtain ⟨e⟩ := segrePresentationLine_powers BX BX B.val B.property m
    exact ⟨(Scheme.Modules.pullbackComp (IntegralModel.Presentations.GraphPolarizationPowers.PolarizationEmbedding.e34Graph X f).left B.val.coefficientEmbedding).symm.app _ ≪≫
      (Scheme.Modules.pullback (IntegralModel.Presentations.GraphPolarizationPowers.PolarizationEmbedding.e34Graph X f).left).mapIso e⟩
  obtain ⟨Q, hQ⟩ := IntegralModel.VaryingProjectiveHilbertPolynomial.PolarizationEmbedding.exists_fixed_varying_e34HilbertPolynomial dims F π hπ (fun _ => 0) L hL
  exact ⟨Q, fun B hB => hQ ⟨B, hB⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.SegreGraphPolynomials
