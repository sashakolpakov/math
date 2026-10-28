import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectionRestriction
import OAI.AlgebraicGeometry.Comparison.Betti.TwistedLaurentObstruction

/-! # Section Equiv -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectionEquiv.Dolbeault

noncomputable section

section

/-! Uniqueness and reconstruction of normalized Laurent decompositions for
actual holomorphic sections over an arbitrary parameter domain. -/

open _root_.TopologicalSpace Set

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]

omit [FiniteDimensional ℂ P] in
theorem laurentSection_fiber_unique (S : Opens P)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen))
    (a b : Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S ⊤))
    (hb0 : ∀ p : S, b.val ⟨(p.val, 0), ⟨p.property, trivial⟩⟩ = 0)
    (h : ∀ x : ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen,
      f.val x = a.val ⟨x.val, ⟨x.property.1, trivial⟩⟩ +
        b.val ⟨(x.val.1, x.val.2⁻¹), ⟨x.property.1, trivial⟩⟩) (p : S) :
    AnnularCauchyFormula.Dolbeault.positiveLaurentPart (fun w => FiberVanishing.Dolbeault.holomorphicFunctionExtension _ f (p.val, w)) =
        (fun w => FiberVanishing.Dolbeault.holomorphicFunctionExtension _ a (p.val, w)) ∧
      Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart (fun w => FiberVanishing.Dolbeault.holomorphicFunctionExtension _ f (p.val, w)) =
        (fun w => FiberVanishing.Dolbeault.holomorphicFunctionExtension _ b (p.val, w)) := by
  apply ProjectionNaturality.Dolbeault.laurentProjection_eq_of_decomposition
    (ParametricPositiveLaurent.Dolbeault.puncturedFamily_slice_holomorphic (FiberVanishing.Dolbeault.holomorphicFunctionExtension_differentiable _ f) p.property)
    (TwistedLaurentObstruction.Dolbeault.entireFamily_slice_holomorphic (FiberVanishing.Dolbeault.holomorphicFunctionExtension_differentiable _ a) p.property)
    (TwistedLaurentObstruction.Dolbeault.entireFamily_slice_holomorphic (FiberVanishing.Dolbeault.holomorphicFunctionExtension_differentiable _ b) p.property)
  · exact (Holomorphic.CoefficientMem.openCoefficientExtension_apply _ b.val ⟨(p.val, 0), ⟨p.property, trivial⟩⟩).trans (hb0 p)
  · intro z hz
    change Holomorphic.CoefficientMem.openCoefficientExtension _ f.val (p.val, z) =
      Holomorphic.CoefficientMem.openCoefficientExtension _ a.val (p.val, z) + Holomorphic.CoefficientMem.openCoefficientExtension _ b.val (p.val, z⁻¹)
    rw [Holomorphic.CoefficientMem.openCoefficientExtension_apply _ f.val ⟨(p.val, z), ⟨p.property, hz⟩⟩,
      Holomorphic.CoefficientMem.openCoefficientExtension_apply _ a.val ⟨(p.val, z), ⟨p.property, trivial⟩⟩,
      Holomorphic.CoefficientMem.openCoefficientExtension_apply _ b.val ⟨(p.val, z⁻¹), ⟨p.property, trivial⟩⟩]
    exact h ⟨(p.val, z), ⟨p.property, hz⟩⟩

theorem laurentSection_eq_of_decomposition (S : Opens P)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen))
    (a b : Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S ⊤))
    (hb0 : ∀ p : S, b.val ⟨(p.val, 0), ⟨p.property, trivial⟩⟩ = 0)
    (h : ∀ x : ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen,
      f.val x = a.val ⟨x.val, ⟨x.property.1, trivial⟩⟩ +
        b.val ⟨(x.val.1, x.val.2⁻¹), ⟨x.property.1, trivial⟩⟩) :
    FiberVanishing.Dolbeault.positiveLaurentSection S f = a ∧ FiberVanishing.Dolbeault.negativeLaurentSection S f = b := by
  constructor
  · apply Subtype.ext
    funext x
    exact (congrFun (laurentSection_fiber_unique S f a b hb0 h ⟨x.val.1, x.property.1⟩).1 x.val.2).trans
      (Holomorphic.CoefficientMem.openCoefficientExtension_apply _ a.val x)
  · apply Subtype.ext
    funext x
    exact (congrFun (laurentSection_fiber_unique S f a b hb0 h ⟨x.val.1, x.property.1⟩).2 x.val.2).trans
      (Holomorphic.CoefficientMem.openCoefficientExtension_apply _ b.val x)

def inverseLaurentSection (S : Opens P) (b : Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S ⊤)) :
    Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen) :=
  PolynomialHolomorphicSections.AnalyticLocal.functionSectionOfDifferentiable (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen)
    (fun q => FiberVanishing.Dolbeault.holomorphicFunctionExtension _ b (q.1, q.2⁻¹)) (by
      intro q hq
      have hb := (FiberVanishing.Dolbeault.holomorphicFunctionExtension_differentiable _ b).differentiableAt
        ((ContractionCauchyPrimitive.Dolbeault.productOpen S ⊤).isOpen.mem_nhds
          (show (q.1, q.2⁻¹) ∈ ContractionCauchyPrimitive.Dolbeault.productOpen S ⊤ from ⟨hq.1, trivial⟩))
      exact (hb.comp q (differentiableAt_fst.prodMk
        (differentiableAt_snd.fun_inv hq.2))).differentiableWithinAt)

theorem inverseLaurentSection_apply (S : Opens P) (b : Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S ⊤))
    (x : ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen) :
    (inverseLaurentSection S b).val x =
      b.val ⟨(x.val.1, x.val.2⁻¹), ⟨x.property.1, trivial⟩⟩ := by
  change Holomorphic.CoefficientMem.openCoefficientExtension _ b.val (x.val.1, x.val.2⁻¹) = _
  exact Holomorphic.CoefficientMem.openCoefficientExtension_apply _ b.val
    ⟨(x.val.1, x.val.2⁻¹), ⟨x.property.1, trivial⟩⟩

def inverseLaurentSectionMap (S : Opens P) :
    Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S ⊤) →ₗ[ℂ]
      Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen) where
  toFun := inverseLaurentSection S
  map_add' a b := by
    apply Subtype.ext
    funext x
    simp only [Pi.add_apply, Subalgebra.coe_add, inverseLaurentSection_apply]
  map_smul' c b := by
    apply Subtype.ext
    funext x
    simp only [Pi.smul_apply, Subalgebra.coe_smul, inverseLaurentSection_apply, RingHom.id_apply]

end

/-! The normalized Laurent decomposition is a genuine complex-linear
equivalence of holomorphic section spaces. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]

def zeroLaurentConstantSections (S : Opens P) :
    Submodule ℂ (Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S ⊤)) where
  carrier := {b | ∀ p : S, b.val ⟨(p.val, 0), ⟨p.property, trivial⟩⟩ = 0}
  zero_mem' := fun _ => rfl
  add_mem' := by
    intro a b ha hb p
    change a.val _ + b.val _ = 0
    rw [ha, hb, add_zero]
  smul_mem' := by
    intro c b hb p
    change c • b.val _ = 0
    rw [hb, smul_zero]

def normalizedNegativeLaurentSectionMap (S : Opens P) :
    Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen) →ₗ[ℂ]
      zeroLaurentConstantSections S :=
  (FiberVanishing.Dolbeault.negativeLaurentSectionMap S).codRestrict (zeroLaurentConstantSections S)
    (FiberVanishing.Dolbeault.negativeLaurentSection_zero S)

def laurentSectionPairMap (S : Opens P) :
    Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen) →ₗ[ℂ]
      Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S ⊤) × zeroLaurentConstantSections S :=
  (FiberVanishing.Dolbeault.positiveLaurentSectionMap S).prod (normalizedNegativeLaurentSectionMap S)

def assembleLaurentSectionMap (S : Opens P) :
    Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S ⊤) × zeroLaurentConstantSections S →ₗ[ℂ]
      Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen) :=
  ((Holomorphic.Restrictions.holomorphicFunctionRestrict (show ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen ≤ ContractionCauchyPrimitive.Dolbeault.productOpen S ⊤ from
    fun _ hx => ⟨hx.1, trivial⟩)).toLinearMap.comp (LinearMap.fst ℂ _ _)) +
      (inverseLaurentSectionMap S).comp
        ((zeroLaurentConstantSections S).subtype.comp (LinearMap.snd ℂ _ _))

theorem assembleLaurentSectionMap_apply (S : Opens P)
    (a : Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S ⊤)) (b : zeroLaurentConstantSections S)
    (x : ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen) :
    (assembleLaurentSectionMap S (a, b)).val x =
      a.val ⟨x.val, ⟨x.property.1, trivial⟩⟩ +
        b.val.val ⟨(x.val.1, x.val.2⁻¹), ⟨x.property.1, trivial⟩⟩ := by
  change a.val _ + (inverseLaurentSection S b.val).val x = _
  rw [inverseLaurentSection_apply]

theorem assembleLaurentSectionPair (S : Opens P)
    (f : Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen)) :
    assembleLaurentSectionMap S (laurentSectionPairMap S f) = f := by
  apply Subtype.ext
  funext x
  rw [show laurentSectionPairMap S f =
    (FiberVanishing.Dolbeault.positiveLaurentSection S f, normalizedNegativeLaurentSectionMap S f) from rfl,
    assembleLaurentSectionMap_apply]
  exact FiberVanishing.Dolbeault.laurentSectionSplitting_identity S f x

theorem laurentSectionPair_assemble (S : Opens P)
    (v : Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S ⊤) × zeroLaurentConstantSections S) :
    laurentSectionPairMap S (assembleLaurentSectionMap S v) = v := by
  obtain ⟨a, b⟩ := v
  have h := laurentSection_eq_of_decomposition S (assembleLaurentSectionMap S (a, b)) a b.val
    b.property (assembleLaurentSectionMap_apply S a b)
  exact Prod.ext h.1 (Subtype.ext h.2)

def laurentSectionEquiv (S : Opens P) :
    Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen) ≃ₗ[ℂ]
      Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S ⊤) × zeroLaurentConstantSections S where
  toLinearMap := laurentSectionPairMap S
  invFun := assembleLaurentSectionMap S
  left_inv := assembleLaurentSectionPair S
  right_inv := laurentSectionPair_assemble S

def nativeLaurentSectionEquiv (S : Opens P) :
    C^∞⟮𝓘(ℂ, P × ℂ), ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen; 𝓘(ℂ), ℂ⟯ ≃ₗ[ℂ]
      Holomorphic.FunctionPure.holomorphicFunctions (ContractionCauchyPrimitive.Dolbeault.productOpen S ⊤) × zeroLaurentConstantSections S :=
  (Holomorphic.StandardFunctionSheaf.AnalyticLocal.holomorphicFunctionContMDiffEquiv (P × ℂ)
    (ContractionCauchyPrimitive.Dolbeault.productOpen S PuncturedCauchy.Dolbeault.puncturedComplexOpen)).symm.toLinearEquiv.trans (laurentSectionEquiv S)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectionEquiv.Dolbeault
