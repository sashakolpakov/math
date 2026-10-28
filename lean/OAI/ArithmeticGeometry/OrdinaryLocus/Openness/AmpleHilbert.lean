import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmpleEmbeddingPower
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PolarizedHilbert
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GlobalSectionDimension
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldPoint

/-! # Ample Hilbert -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmpleHilbert.Construction

noncomputable section

/-! Eventual Hilbert polynomials along positive powers of any ample line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ample_sections_eventuallyPolynomial
    {X S : Scheme.{0}} [IsAffine S] (f : X ⟶ S) [IsProper f]
    (hfield : IsField Γ(S, ⊤)) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : L.IsAmple) :
    ∃ d : ℕ, 0 < d ∧ ∃ r : ℕ,
      ∀ (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType],
        AlgebraicGeometry.SheafCohomology.Projective.BoundedEventualPolynomial.EventuallyPolynomialOfDegree (fun n =>
          (Module.finrank Γ(S, ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).obj
            (SheafTensor.Construction.sheafTensor M (L.tensorPower (n * d)).sheaf)) : ℚ)) r := by
  let R := Γ(S, ⊤)
  let : Field R := hfield.toField
  let : Field Γ(Spec (.of R), ⊤) := AlgebraicGeometry.Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField R
  have : IsIso S.toSpecΓ.appTop := by
    rw [Scheme.toSpecΓ_appTop]
    infer_instance
  obtain ⟨d, hd, r, a, ha, hb, ⟨e⟩⟩ := AmpleEmbeddingPower.Construction.ample_exists_closed_embedding_power f L hL
  have : IsClosedImmersion a := ha
  refine ⟨d, hd, r, fun M _ _ => ?_⟩
  obtain ⟨P, hP, b, hp⟩ := PolarizedHilbert.Construction.coordinateBundle_sections_eventuallyPolynomial a M 0
    (L.tensorPower d) e (Field.toIsField _)
  refine ⟨P, hP, b, fun n hn => ?_⟩
  let N := SheafTensor.Construction.sheafTensor M ((L.tensorPower d).tensorPower n).sheaf
  have hbase : Module.finrank Γ(Spec (.of R), ⊤)
      ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (a ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)).obj N) =
      Module.finrank R ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).obj N) :=
    (GlobalSectionDimension.Construction.baseGlobalSections_finrank_congr hb N).trans (GlobalSectionDimension.Construction.baseGlobalSections_finrank_comp f S.toSpecΓ N)
  let eN : N ≅ SheafTensor.Construction.sheafTensor M (L.tensorPower (n * d)).sheaf :=
    SheafTensor.Construction.sheafTensorCongr (Iso.refl M) (L.tensorPowerComposeIso n d).symm
  have hdims := ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).mapIso eN).toLinearEquiv.finrank_eq
  have heq := hbase.trans hdims
  exact (congrArg (fun k : ℕ => (k : ℚ)) heq).symm.trans (hp n hn)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmpleHilbert.Construction
