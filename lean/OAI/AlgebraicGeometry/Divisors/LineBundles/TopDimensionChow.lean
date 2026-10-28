import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.DimensionGeneric
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.PushforwardDimensionDrop
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowRestriction

/-! # Top Dimension Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.TopDimensionChow.BundleCycles

noncomputable section

/-! On an integral scheme, top-dimensional Chow classes have no
principal relations and are detected on every nonempty open. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

omit [AlgebraicGeometry.IsNoetherian X] in
theorem integralSupport_dimension_le (W : IrreducibleCloseds X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  have h := Principal.PushforwardDimensionDrop.BundleCycles.pointDimension_le_schemeDimension f (irreducibleSetEquivPoints W)
  simpa only [irreducibleSetEquivPoints.symm_apply_apply] using h

theorem dimensionRationalEquivalenceQ_top_eq_bot (d : ℕ)
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f ≤ d) : DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro z ⟨W, hW, g, hg, rfl⟩
  have h := integralSupport_dimension_le f W
  omega

theorem dimensionCycleToChowQ_top_injective (d : ℕ)
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f ≤ d) : Function.Injective (DimensionChow.BundleCycles.dimensionCycleToChowQ f d) := by
  apply LinearMap.ker_eq_bot.mp
  change LinearMap.ker (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d).mkQ = ⊥
  rw [Submodule.ker_mkQ, dimensionRationalEquivalenceQ_top_eq_bot f d hd]

theorem openChowRestriction_top_injective {U : Scheme.{0}} [IsIntegral U]
    [AlgebraicGeometry.IsNoetherian U] (i : U ⟶ X) [IsOpenImmersion i]
    (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d) :
    Function.Injective (Open.ChowRestriction.BundleCycles.openChowRestriction i f d) := by
  have hU : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ f) = d :=
    (Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion i f).trans hd
  intro α β h
  obtain ⟨a, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d α
  obtain ⟨b, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d β
  rw [Open.ChowRestriction.BundleCycles.openChowRestriction_cycle, Open.ChowRestriction.BundleCycles.openChowRestriction_cycle] at h
  have hab := dimensionCycleToChowQ_top_injective (i ≫ f) d hU.le h
  congr 1
  ext x
  have hx : x.val = genericPoint X := Point.DimensionGeneric.BundleCycles.point_eq_generic_of_dimension_eq f x.val (x.property.trans hd.symm)
  let y : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d :=
    ⟨genericPoint U, (ImmersionDimension.BundleCycles.pointClosure_dimension_immersion i f _).symm.trans
      ((congrArg (fun z => Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm z) f)
        (genericPoint_eq_of_isOpenImmersion i)).trans (hx ▸ x.property))⟩
  have he : Open.CycleRestriction.BundleCycles.openDimensionPointEmbedding i f d y = x :=
    Subtype.ext ((genericPoint_eq_of_isOpenImmersion i).trans hx.symm)
  have hv := congrArg (fun z => z y) hab
  change a (Open.CycleRestriction.BundleCycles.openDimensionPointEmbedding i f d y) = b (Open.CycleRestriction.BundleCycles.openDimensionPointEmbedding i f d y) at hv
  rwa [he] at hv

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.TopDimensionChow.BundleCycles
