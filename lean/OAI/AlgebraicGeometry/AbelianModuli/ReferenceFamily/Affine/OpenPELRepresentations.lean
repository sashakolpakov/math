import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PELActionBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.BaseFunctorRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.RelativePELRepresentation
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Open PEL Representations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OpenPELRepresentations

noncomputable section

/-! Constructed bounded PEL-action representations on affine opens of an
arbitrary noetherian parameter base, expressed in the original functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [Algebra ℚ R] {s N : ℕ} (P : Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)

theorem exists_affine_open_pel_representation [IsNoetherian M.left]
    (D : PELModuli.IntegralModel.CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    (hc : ∀ x : M.left, IsUnit (D.conductor : M.left.presheaf.stalk x))
    (U : M.left.Opens) [IsAffine U.toScheme] :
    ∃ C : Open.Representations.OpenRepresentation (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A) U,
      LocallyOfFiniteType C.space.hom ∧ QuasiCompact C.space.hom ∧ IsSeparated C.space.hom := by
  let MU : Over (Spec (.of R)) := Over.mk (U.ι ≫ M.hom)
  let _ : IsAffine MU.left := inferInstanceAs (IsAffine U.toScheme)
  let _ : IsLocallyNoetherian MU.left := inferInstanceAs (IsLocallyNoetherian U.toScheme)
  have hcU : ∀ x : U.toScheme, IsUnit (D.conductor : U.toScheme.presheaf.stalk x) := fun x => by
    simpa only [map_natCast] using (hc (U.ι x)).map (U.ι.stalkMap x).hom
  obtain ⟨Z, hft, hqc, hs, u, hclass⟩ :=
    RelativePELRepresentation.exists_affine_relative_pel_action_representation P iotaO MU (A.pullback U.ι) D hcU
  let _ : LocallyOfFiniteType Z.hom := hft
  let _ : QuasiCompact Z.hom := hqc
  let _ : IsSeparated Z.hom := hs
  let e := PELModuli.IntegralModel.Relative.PELActionBaseChange.ActionBaseChange.relativePELActionFunctorIso P iotaO M A U.ι
  let u' := e.hom.app (op Z) u
  have hclass' (T : Over U.toScheme) : Function.Bijective
      (fun f : T ⟶ Z => (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).map ((Over.map U.ι).map f).op u') :=
    PELModuli.IntegralModel.Open.BaseFunctorRepresentation.representation_bijective_of_iso e Z u T (hclass T)
  let C := Open.BaseFunctorRepresentation.openRepresentationOfBase (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A) U Z u' hclass'
  refine ⟨C, ?_, ?_, ?_⟩
  · exact inferInstanceAs (LocallyOfFiniteType (Z.hom ≫ U.ι))
  · exact inferInstanceAs (QuasiCompact (Z.hom ≫ U.ι))
  · exact inferInstanceAs (IsSeparated (Z.hom ≫ U.ι))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.OpenPELRepresentations
