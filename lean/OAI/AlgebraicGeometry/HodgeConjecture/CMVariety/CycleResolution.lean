import OAI.AlgebraicGeometry.Cycles.Functoriality.UnitCap
import OAI.AlgebraicGeometry.Foundations.Scheme.OpenFunctionField

/-! # Cycle Resolution -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.CycleResolution.CM.Abelian

noncomputable section

/-! Resolve each actual irreducible cycle support, with its required dimension equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- The exact committed Blowups resolution statement, retained as a named input. -/
def ResolutionInput : Prop :=
  ∀ (X : Scheme) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X]
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f),
    letI : LocallyOfFinitePresentation f := P.locallyOfFinitePresentation
    ∃ (R : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : R.carrier ⟶ X),
      π ≫ f = R.structureMap ∧ IsProper π ∧
      (∃ e : R.carrier.PartialIso X,
        e.source.ι ≫ π = e.iso.hom ≫ e.target.ι) ∧
      IsIso (π ∣_ f.smoothLocus)

/-- The exact committed resolution clause of Functoriality. -/
def ResolutionClassInput : Prop :=
  ∀ {R X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) (g : R.toOver ⟶ X.toOver) (hg : IsProper g.left)
    (_hres : Cycles.Functoriality.UnitCap.Resolves g Z)
    (hdeg : 0 + X.complexDimension = p + R.complexDimension),
    Z.geometricCycleClass = Cycles.Functoriality.UnitCap.cohomologyPushforward g hg 0 p hdeg (Cycles.Functoriality.UnitCap.cohomologyUnit R)

theorem transcendenceDimension_eq_of_partialIso
    {S T : Scheme} [IsIntegral S] [IsIntegral T]
    (fS : S ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (fT : T ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (π : S ⟶ T) (hπ : π ≫ fT = fS)
    (e : S.PartialIso T) (he : e.source.ι ≫ π = e.iso.hom ≫ e.target.ι) :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension fS = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension fT := by
  let : Nonempty e.source := e.dense_source.nonempty.to_subtype
  let : Nonempty e.target := e.dense_target.nonempty.to_subtype
  calc
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension fS =
        Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (e.source.ι ≫ fS) :=
      (Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_open fS e.source).symm
    _ = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (e.iso.hom ≫ e.target.ι ≫ fT) := by
      rw [← hπ, ← Category.assoc, he, Category.assoc]
    _ = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (e.target.ι ≫ fT) :=
      Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion e.iso.hom _
    _ = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension fT := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_open fT e.target

theorem cycleSupport_has_resolution (hBlowups : ResolutionInput)
    {X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) :
    ∃ (R : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (g : R.toOver ⟶ X.toOver),
      IsProper g.left ∧ Cycles.Functoriality.UnitCap.Resolves g Z ∧
        0 + X.complexDimension = p + R.complexDimension := by
  obtain ⟨R, π, hπ, hproper, ⟨e, he⟩, _⟩ :=
    hBlowups Z.scheme Z.structureMap Z.projectivePresentation
  let : IsProper π := hproper
  let g : R.toOver ⟶ X.toOver := Over.homMk (π ≫ Z.inclusion) (by
    change (π ≫ Z.inclusion) ≫ X.structureMap = R.structureMap
    rw [Category.assoc]
    exact hπ)
  have hdim : R.complexDimension = Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap := by
    rw [R.complexDimension_eq_transcendenceDimension]
    exact transcendenceDimension_eq_of_partialIso R.structureMap Z.structureMap π hπ e he
  refine ⟨R, g, (show IsProper (π ≫ Z.inclusion) from inferInstance),
    ⟨π, rfl, hπ, hproper, e, he⟩, ?_⟩
  have hz := Z.dimension_add_codimension
  rw [← X.complexDimension_eq_transcendenceDimension, ← hdim] at hz
  omega

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.CycleResolution.CM.Abelian
