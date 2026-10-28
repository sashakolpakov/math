import OAI.AlgebraicGeometry.Comparison.Betti.ParametricLaurentSplitting
import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.ProjectionNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionPure
import OAI.AlgebraicGeometry.Comparison.Betti.ContractionCauchyPrimitive
import OAI.AlgebraicGeometry.Comparison.Betti.PolynomialHolomorphicSections

/-! # Fiber Vanishing -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Laurent.FiberVanishing.Dolbeault

noncomputable section

section

/-! The normalized Laurent decomposition acts on actual holomorphic sections
over a punctured coordinate line, preserving holomorphic parameters. -/

open _root_.TopologicalSpace Set
open scoped ContDiff

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionPure

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]

def holomorphicFunctionExtension (U : Opens P) (f : Holomorphic.FunctionPure.holomorphicFunctions U) : P → ℂ :=
  Holomorphic.CoefficientMem.openCoefficientExtension U f.val

theorem holomorphicFunctionExtension_differentiable (U : Opens P) (f : Holomorphic.FunctionPure.holomorphicFunctions U) :
    DifferentiableOn ℂ (holomorphicFunctionExtension U f) U :=
  (show ContDiffOn ℂ ∞ (holomorphicFunctionExtension U f) U from f.property).differentiableOn
    (by simp)

theorem holomorphicFunctionExtension_add (U : Opens P) (f g : Holomorphic.FunctionPure.holomorphicFunctions U) :
    holomorphicFunctionExtension U (f + g) =
      holomorphicFunctionExtension U f + holomorphicFunctionExtension U g := by
  funext x
  by_cases hx : x ∈ U <;> simp [holomorphicFunctionExtension, Holomorphic.CoefficientMem.openCoefficientExtension, hx]

theorem holomorphicFunctionExtension_smul (U : Opens P) (c : ℂ) (f : Holomorphic.FunctionPure.holomorphicFunctions U) :
    holomorphicFunctionExtension U (c • f) = c • holomorphicFunctionExtension U f := by
  funext x
  by_cases hx : x ∈ U <;> simp [holomorphicFunctionExtension, Holomorphic.CoefficientMem.openCoefficientExtension, hx]

variable [FiniteDimensional ℂ P]

def positiveLaurentSection (S : Opens P) (f : Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen)) :
    Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S ⊤) :=
  PolynomialHolomorphicSections.AnalyticLocal.functionSectionOfDifferentiable (ContractionCauchyPrimitive.Dolbeault.productOpen S ⊤)
    (ParametricPositiveLaurent.Dolbeault.positiveLaurentFamily (holomorphicFunctionExtension _ f))
    (ParametricPositiveLaurent.Dolbeault.positiveLaurentFamily_holomorphic S.isOpen (holomorphicFunctionExtension_differentiable _ f))

def negativeLaurentSection (S : Opens P) (f : Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen)) :
    Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S ⊤) :=
  PolynomialHolomorphicSections.AnalyticLocal.functionSectionOfDifferentiable (ContractionCauchyPrimitive.Dolbeault.productOpen S ⊤)
    (ParametricLaurentSplitting.Dolbeault.negativeLaurentFamily (holomorphicFunctionExtension _ f))
    (ParametricLaurentSplitting.Dolbeault.negativeLaurentFamily_holomorphic S.isOpen (holomorphicFunctionExtension_differentiable _ f))

theorem positiveLaurentSection_add (S : Opens P)
    (f g : Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen)) :
    positiveLaurentSection S (f + g) = positiveLaurentSection S f + positiveLaurentSection S g := by
  apply Subtype.ext
  funext x
  change AnnularCauchyFormula.Dolbeault.positiveLaurentPart (fun w => holomorphicFunctionExtension _ (f + g) (x.val.1, w)) x.val.2 = _
  rw [holomorphicFunctionExtension_add]
  exact congrFun (ProjectionNaturality.Dolbeault.laurentProjection_add
    (ParametricPositiveLaurent.Dolbeault.puncturedFamily_slice_holomorphic (holomorphicFunctionExtension_differentiable _ f) x.property.1)
    (ParametricPositiveLaurent.Dolbeault.puncturedFamily_slice_holomorphic (holomorphicFunctionExtension_differentiable _ g) x.property.1)).1 x.val.2

theorem negativeLaurentSection_add (S : Opens P)
    (f g : Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen)) :
    negativeLaurentSection S (f + g) = negativeLaurentSection S f + negativeLaurentSection S g := by
  apply Subtype.ext
  funext x
  change Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart (fun w => holomorphicFunctionExtension _ (f + g) (x.val.1, w)) x.val.2 = _
  rw [holomorphicFunctionExtension_add]
  exact congrFun (ProjectionNaturality.Dolbeault.laurentProjection_add
    (ParametricPositiveLaurent.Dolbeault.puncturedFamily_slice_holomorphic (holomorphicFunctionExtension_differentiable _ f) x.property.1)
    (ParametricPositiveLaurent.Dolbeault.puncturedFamily_slice_holomorphic (holomorphicFunctionExtension_differentiable _ g) x.property.1)).2 x.val.2

theorem positiveLaurentSection_smul (S : Opens P) (c : ℂ)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen)) :
    positiveLaurentSection S (c • f) = c • positiveLaurentSection S f := by
  apply Subtype.ext
  funext x
  change AnnularCauchyFormula.Dolbeault.positiveLaurentPart (fun w => holomorphicFunctionExtension _ (c • f) (x.val.1, w)) x.val.2 = _
  rw [holomorphicFunctionExtension_smul]
  exact congrFun (ProjectionNaturality.Dolbeault.laurentProjection_const_mul
    (ParametricPositiveLaurent.Dolbeault.puncturedFamily_slice_holomorphic (holomorphicFunctionExtension_differentiable _ f) x.property.1) c).1 x.val.2

theorem negativeLaurentSection_smul (S : Opens P) (c : ℂ)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen)) :
    negativeLaurentSection S (c • f) = c • negativeLaurentSection S f := by
  apply Subtype.ext
  funext x
  change Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart (fun w => holomorphicFunctionExtension _ (c • f) (x.val.1, w)) x.val.2 = _
  rw [holomorphicFunctionExtension_smul]
  exact congrFun (ProjectionNaturality.Dolbeault.laurentProjection_const_mul
    (ParametricPositiveLaurent.Dolbeault.puncturedFamily_slice_holomorphic (holomorphicFunctionExtension_differentiable _ f) x.property.1) c).2 x.val.2

def positiveLaurentSectionMap (S : Opens P) :
    Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen) →ₗ[ℂ]
      Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S ⊤) where
  toFun := positiveLaurentSection S
  map_add' := positiveLaurentSection_add S
  map_smul' := positiveLaurentSection_smul S

def negativeLaurentSectionMap (S : Opens P) :
    Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen) →ₗ[ℂ]
      Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S ⊤) where
  toFun := negativeLaurentSection S
  map_add' := negativeLaurentSection_add S
  map_smul' := negativeLaurentSection_smul S

theorem negativeLaurentSection_zero (S : Opens P)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen)) (p : S) :
    (negativeLaurentSection S f).val ⟨(p.val, 0), ⟨p.property, trivial⟩⟩ = 0 := by
  change Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart (fun w => holomorphicFunctionExtension _ f (p.val, w)) 0 = 0
  exact Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart_zero _

theorem laurentSectionSplitting_identity (S : Opens P)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen))
    (x : ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen) :
    (positiveLaurentSection S f).val ⟨x.val, ⟨x.property.1, trivial⟩⟩ +
      (negativeLaurentSection S f).val ⟨(x.val.1, x.val.2⁻¹), ⟨x.property.1, trivial⟩⟩ = f.val x :=
  (ParametricLaurentSplitting.Dolbeault.parametricLaurentSplitting_identity (holomorphicFunctionExtension _ f) x.val.1 x.property.2).trans
    (Holomorphic.CoefficientMem.openCoefficientExtension_apply _ f.val x)

end

/-! Both normalized Laurent projections vanish on a parameter fiber whenever
the original holomorphic section vanishes on that entire punctured fiber. -/

open _root_.TopologicalSpace Set

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionPure

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]

theorem laurentSection_fiber_zero (S : Opens P)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen)) (p : S)
    (h : ∀ z : ℂ, ∀ hz : z ≠ 0, f.val ⟨(p.val, z), ⟨p.property, hz⟩⟩ = 0) (w : ℂ) :
    (positiveLaurentSection S f).val ⟨(p.val, w), ⟨p.property, trivial⟩⟩ = 0 ∧
      (negativeLaurentSection S f).val ⟨(p.val, w), ⟨p.property, trivial⟩⟩ = 0 := by
  let g : ℂ → ℂ := fun z => holomorphicFunctionExtension _ f (p.val, z)
  have hg : DifferentiableOn ℂ g (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ) :=
    ParametricPositiveLaurent.Dolbeault.puncturedFamily_slice_holomorphic (holomorphicFunctionExtension_differentiable _ f) p.property
  have hzero : ∀ z ≠ 0, g z = (0 : ℂ) := by
    intro z hz
    exact (Holomorphic.CoefficientMem.openCoefficientExtension_apply _ f.val ⟨(p.val, z), ⟨p.property, hz⟩⟩).trans (h z hz)
  have hc := ProjectionNaturality.Dolbeault.laurentProjection_congr hg (differentiable_const (0 : ℂ)).differentiableOn hzero
  have hz := ProjectionNaturality.Dolbeault.laurentProjection_entire (differentiable_const (0 : ℂ))
  exact ⟨congrFun (hc.1.trans hz.1) w, congrFun (hc.2.trans hz.2) w⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Laurent.FiberVanishing.Dolbeault
