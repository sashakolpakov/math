import OAI.NumberTheory.PadicHodge.WeakAdmissibility.FilteredRepresentations

/-! # Linear -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Linear

noncomputable section

/-! Linear constructions for GeometricComparison. The filtration and numerical conditions
are defined independently of comparison or geometric admissibility. -/

open scoped TensorProduct

universe u v w

abbrev FiniteFiltration := WeakAdmissibility.FilteredRepresentations.Construction.FiniteFiltration

/-- The numerical definition over the split base field, with v_q(q) = 1.
Every Frobenius-stable rational subspace is tested. -/
def WeaklyAdmissible (q : ℕ) [Fact q.Prime]
    {D : Type u} [AddCommGroup D] [Module ℚ_[q] D]
    [FiniteDimensional ℚ_[q] D]
    (Fil : FiniteFiltration ℚ_[q] D) (φ : D ≃ₗ[ℚ_[q]] D) : Prop :=
  Fil.tH = (Padic.valuation (LinearMap.det φ.toLinearMap) : ℚ) ∧
    ∀ (S : Submodule ℚ_[q] D) (hS : S ≤ S.comap φ.toLinearMap),
      (Fil.restrict S).tH ≤
        (Padic.valuation (LinearMap.det (φ.toLinearMap.restrict hS)) : ℚ)

/-- Simultaneous generalized eigenspace; no semisimplicity is imposed. -/
def generalizedHeckeSummand {L : Type u} [Field L]
    {D : Type v} [AddCommGroup D] [Module L D]
    {I : Type w} (T : I → Module.End L D) (χ : I → L) : Submodule L D :=
  ⨅ i, (T i).maxGenEigenspace (χ i)

theorem mem_generalizedHeckeSummand {L : Type u} [Field L]
    {D : Type v} [AddCommGroup D] [Module L D]
    {I : Type w} (T : I → Module.End L D) (χ : I → L) (x : D) :
    x ∈ generalizedHeckeSummand T χ ↔
      ∀ i, x ∈ (T i).maxGenEigenspace (χ i) := by
  simp only [generalizedHeckeSummand, Submodule.mem_iInf]

/-- A finite field of coefficients inside the specified algebraic closure.
The only conditions are field finiteness and containment of eigenvalues. -/
structure FiniteHeckeCoefficientField (q : ℕ) [Fact q.Prime]
    {I : Type u} (χ : I → AlgebraicClosure ℚ_[q]) where
  field : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q])
  finite : FiniteDimensional ℚ_[q] field
  contains : ∀ i, χ i ∈ field

attribute [instance] FiniteHeckeCoefficientField.finite

namespace FiniteHeckeCoefficientField

variable {q : ℕ} [Fact q.Prime] {I : Type u}
  {χ : I → AlgebraicClosure ℚ_[q]} (L : FiniteHeckeCoefficientField q χ)

def character (i : I) : L.field := ⟨χ i, L.contains i⟩

@[simp] theorem character_coe (i : I) :
    (L.character i : AlgebraicClosure ℚ_[q]) = χ i := rfl

end FiniteHeckeCoefficientField

/-- A finite list of algebraic local eigenvalues has a canonical finite
coefficient field: the field they generate over ℚ_q. -/
def finiteCoefficientFieldOfFiniteFamily (q : ℕ) [Fact q.Prime]
    {I : Type u} [Finite I] (χ : I → AlgebraicClosure ℚ_[q]) :
    FiniteHeckeCoefficientField q χ where
  field := IntermediateField.adjoin ℚ_[q] (Set.range χ)
  finite := IntermediateField.finiteDimensional_adjoin (fun x _ =>
    Algebra.IsIntegral.isIntegral x)
  contains i := IntermediateField.subset_adjoin ℚ_[q] (Set.range χ) (Set.mem_range_self i)

variable {K : Type u} [Field K] (L : Type v) [Field L] [Algebra K L]
  {D : Type w} [AddCommGroup D] [Module K D]

/-- Scalar extension carries the original Frobenius and the identity on L. -/
def coefficientFrobenius (φ : Module.End K D) :
    Module.End L (L ⊗[K] D) := φ.baseChange L

@[simp] theorem coefficientFrobenius_tmul (φ : Module.End K D) (a : L) (x : D) :
    coefficientFrobenius L φ (a ⊗ₜ[K] x) = a ⊗ₜ[K] φ x := rfl

/-- Filtration subspaces are extended by the canonical tensor map. -/
def coefficientFiltration (Fil : ℤ → Submodule K D) (i : ℤ) :
    Submodule L (L ⊗[K] D) := (Fil i).baseChange L

/-- Extend the given finite filtration without selecting a basis. -/
def finiteCoefficientFiltration (Fil : FiniteFiltration K D) :
    FiniteFiltration L (L ⊗[K] D) where
  step i := (Fil.step i).baseChange L
  antitone_step _ _ hij := Submodule.baseChange_mono L (Fil.antitone_step hij)
  eventually_top := by
    obtain ⟨i, hi⟩ := Fil.eventually_top
    exact ⟨i, by simp [hi]⟩
  eventually_bot := by
    obtain ⟨i, hi⟩ := Fil.eventually_bot
    exact ⟨i, by simp [hi]⟩

/-- Restrict the scalars of a finite filtration, retaining the same subsets. -/
def restrictScalarFiltration {V : Type*} [AddCommGroup V] [Module L V]
    [Module K V] [IsScalarTower K L V] (Fil : FiniteFiltration L V) :
    FiniteFiltration K V where
  step i := (Fil.step i).restrictScalars K
  antitone_step _ _ hij := Submodule.restrictScalars_mono K (Fil.antitone_step hij)
  eventually_top := by
    obtain ⟨i, hi⟩ := Fil.eventually_top
    exact ⟨i, by simp [hi]⟩
  eventually_bot := by
    obtain ⟨i, hi⟩ := Fil.eventually_bot
    exact ⟨i, by simp [hi]⟩

/-- The filtration used for weak admissibility of a coefficient summand. -/
def coefficientSummandFiltration (Fil : FiniteFiltration K D)
    (S : Submodule L (L ⊗[K] D)) : FiniteFiltration K S :=
  restrictScalarFiltration L ((finiteCoefficientFiltration L Fil).restrict S)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Linear
