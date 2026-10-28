import OAI.AlgebraicGeometry.PELModuli.CMPoints.PresentationsTupleParameters

/-! # Bounded Endomorphism Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.BoundedEndomorphismDescent

noncomputable section

/-! Decode the descended point of the actual Presentations endomorphism locus.
Naturality gives equality with the specified complex endomorphisms after
the canonical geometric restriction, on the same arithmetic model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem e34_bounded_endomorphism_tuple_descends
    {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
    {g n : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K)))
    {B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.scheme ⨯ A.scheme)}
    {P : Fin n → Polynomial ℚ}
    {L : HilbertScheme.Presentations.Loci.Core.HilbertHomLoci A.scheme A.scheme B n P}
    {R : HilbertScheme.Presentations.Endomorphisms.Core.FiniteEndomorphismEquations A.scheme n}
    (M : HilbertScheme.Presentations.Loci.Core.EndomorphismEquationLoci A.scheme B n P L R)
    (V : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : V.toOver ≅ (A.pullback (Spec.map (CommRingCat.ofHom κ))).scheme)
    [IsMonHom e.hom]
    (r : Fin n → IntegralModel.Finite.Actions.GroupEndRing (A.pullback (Spec.map (CommRingCat.ofHom κ))))
    (hr : HilbertScheme.Presentations.Has.Core.HasGraphPolynomials A.scheme A.scheme n B P
      (fun i => IntegralModel.EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A (Over.mk (Spec.map (CommRingCat.ofHom κ)))
        ((r i).hom _))) :
    ∃ (F : IntegralModel.Base.ArithmeticBaseExtension K κ)
      (rF : Fin n → IntegralModel.Finite.Actions.GroupEndRing (A.pullback F.fieldExtension)),
      F.denominator = 1 ∧ ∀ i, IntegralModel.EndomorphismFamiliesId.EndomorphismFamilies.restrict A F.complexFieldMap (rF i) = r i := by
  let T : Over (Spec (.of K)) := Over.mk (Spec.map (CommRingCat.ofHom κ))
  let p : T ⟶ M.endScheme := PresentationsTupleParameters.e34TuplePoint A M T r hr
  obtain ⟨F, pF, hF, hpF⟩ := EndomorphismParameterDescent.e34_endomorphism_parameter_descends κ A M V e p
  refine ⟨F, PresentationsTupleParameters.e34TupleValue A M (Over.mk F.fieldExtension) pF, hF, fun i => ?_⟩
  exact (PresentationsTupleParameters.e34TupleValue_restriction A M F.complexFieldMap pF i).trans
    ((congrArg (fun q => PresentationsTupleParameters.e34TupleValue A M T q i) hpF).trans
      (PresentationsTupleParameters.e34TupleValue_point A M T r hr i))

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.BoundedEndomorphismDescent
