import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.FiberVanishing
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Restrictions

/-! # Section Restriction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectionRestriction.Dolbeault

noncomputable section

/-! The actual Laurent section operators commute with restriction of the
holomorphic parameter domain. -/

open _root_.TopologicalSpace Set

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Restrictions

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]

theorem holomorphicFunctionExtension_restrict_at {U V : Opens P} (h : V ≤ U)
    (f : Holomorphic.FunctionPure.holomorphicFunctions U) (x : V) :
    FiberVanishing.Dolbeault.holomorphicFunctionExtension V (Holomorphic.Restrictions.holomorphicFunctionRestrict h f) x.val =
      FiberVanishing.Dolbeault.holomorphicFunctionExtension U f x.val := by
  rw [FiberVanishing.Dolbeault.holomorphicFunctionExtension, Holomorphic.CoefficientMem.openCoefficientExtension_apply V _ x]
  rw [FiberVanishing.Dolbeault.holomorphicFunctionExtension, Holomorphic.CoefficientMem.openCoefficientExtension_apply U _ (Opens.inclusion h x)]
  rfl

omit [NormedSpace ℂ P] in
theorem productOpen_mono_left {S T : Opens P} (h : T ≤ S) (U : Opens ℂ) :
    ContractionCauchyPrimitive.Dolbeault.productOpen T U ≤ ContractionCauchyPrimitive.Dolbeault.productOpen S U := fun _ hx => ⟨h hx.1, hx.2⟩

variable [FiniteDimensional ℂ P]

omit [FiniteDimensional ℂ P] in
theorem laurentSection_restrict_values {S T : Opens P} (h : T ≤ S)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen)) (p : T) :
    AnnularCauchyFormula.Dolbeault.positiveLaurentPart (fun w => FiberVanishing.Dolbeault.holomorphicFunctionExtension _
        (Holomorphic.Restrictions.holomorphicFunctionRestrict (productOpen_mono_left h PuncturedCauchy.Dolbeault.puncturedComplexOpen) f) (p.val, w)) =
        AnnularCauchyFormula.Dolbeault.positiveLaurentPart (fun w => FiberVanishing.Dolbeault.holomorphicFunctionExtension _ f (p.val, w)) ∧
      Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart (fun w => FiberVanishing.Dolbeault.holomorphicFunctionExtension _
        (Holomorphic.Restrictions.holomorphicFunctionRestrict (productOpen_mono_left h PuncturedCauchy.Dolbeault.puncturedComplexOpen) f) (p.val, w)) =
        Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart (fun w => FiberVanishing.Dolbeault.holomorphicFunctionExtension _ f (p.val, w)) := by
  apply ProjectionNaturality.Dolbeault.laurentProjection_congr
    (ParametricPositiveLaurent.Dolbeault.puncturedFamily_slice_holomorphic (FiberVanishing.Dolbeault.holomorphicFunctionExtension_differentiable _ _) p.property)
    (ParametricPositiveLaurent.Dolbeault.puncturedFamily_slice_holomorphic (FiberVanishing.Dolbeault.holomorphicFunctionExtension_differentiable _ f) (h p.property))
  intro w hw
  exact holomorphicFunctionExtension_restrict_at (productOpen_mono_left h PuncturedCauchy.Dolbeault.puncturedComplexOpen) f
    ⟨(p.val, w), ⟨p.property, hw⟩⟩

theorem positiveLaurentSection_restrict {S T : Opens P} (h : T ≤ S)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen)) :
    FiberVanishing.Dolbeault.positiveLaurentSection T
        (Holomorphic.Restrictions.holomorphicFunctionRestrict (productOpen_mono_left h PuncturedCauchy.Dolbeault.puncturedComplexOpen) f) =
      Holomorphic.Restrictions.holomorphicFunctionRestrict (productOpen_mono_left h ⊤) (FiberVanishing.Dolbeault.positiveLaurentSection S f) := by
  apply Subtype.ext
  funext x
  exact congrFun (laurentSection_restrict_values h f ⟨x.val.1, x.property.1⟩).1 x.val.2

theorem negativeLaurentSection_restrict {S T : Opens P} (h : T ≤ S)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen)) :
    FiberVanishing.Dolbeault.negativeLaurentSection T
        (Holomorphic.Restrictions.holomorphicFunctionRestrict (productOpen_mono_left h PuncturedCauchy.Dolbeault.puncturedComplexOpen) f) =
      Holomorphic.Restrictions.holomorphicFunctionRestrict (productOpen_mono_left h ⊤) (FiberVanishing.Dolbeault.negativeLaurentSection S f) := by
  apply Subtype.ext
  funext x
  exact congrFun (laurentSection_restrict_values h f ⟨x.val.1, x.property.1⟩).2 x.val.2

theorem positiveLaurentSectionMap_restrict {S T : Opens P} (h : T ≤ S) :
    (FiberVanishing.Dolbeault.positiveLaurentSectionMap T).comp
        (Holomorphic.Restrictions.holomorphicFunctionRestrict (productOpen_mono_left h PuncturedCauchy.Dolbeault.puncturedComplexOpen)).toLinearMap =
      (Holomorphic.Restrictions.holomorphicFunctionRestrict (productOpen_mono_left h ⊤)).toLinearMap.comp
        (FiberVanishing.Dolbeault.positiveLaurentSectionMap S) := by
  apply LinearMap.ext
  exact positiveLaurentSection_restrict h

theorem negativeLaurentSectionMap_restrict {S T : Opens P} (h : T ≤ S) :
    (FiberVanishing.Dolbeault.negativeLaurentSectionMap T).comp
        (Holomorphic.Restrictions.holomorphicFunctionRestrict (productOpen_mono_left h PuncturedCauchy.Dolbeault.puncturedComplexOpen)).toLinearMap =
      (Holomorphic.Restrictions.holomorphicFunctionRestrict (productOpen_mono_left h ⊤)).toLinearMap.comp
        (FiberVanishing.Dolbeault.negativeLaurentSectionMap S) := by
  apply LinearMap.ext
  exact negativeLaurentSection_restrict h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectionRestriction.Dolbeault
