import OAI.Analysis.HodgeTheory.Decomposition.KahlerCommutator
import OAI.Analysis.HodgeTheory.Decomposition.ComplexMetric

/-! # Connection Symbols -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionSymbols

noncomputable section

/-! The genuine covector connection with a complex line-connection term, and its exact symbols. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def lineConnectionTerm (n : ℕ) (A : E →L[ℝ] ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n :=
  ((ContinuousLinearMap.lsmul ℝ ℂ).flip a).comp A

theorem lineConnectionTerm_apply (n : ℕ) (A : E →L[ℝ] ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (v : E) :
    lineConnectionTerm n A a v = A v • a := rfl

def lineCovectorConnectionDerivative (n : ℕ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n :=
  Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative n Γ a x + lineConnectionTerm n (A x) (a x)

theorem lineCovectorConnectionDerivative_apply (n : ℕ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x v : E) :
    lineCovectorConnectionDerivative n Γ A a x v =
      Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative n Γ a x v + A x v • a x := rfl

def lineExteriorDerivative (n : ℕ) (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) : Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1) :=
  extDeriv a x + ContinuousAlternatingMap.alternatizeUncurryFin (lineConnectionTerm n (A x) (a x))

def lineTwistedExteriorDerivative (n : ℕ) (J : E →L[ℝ] E)
    (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) : Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1) :=
  Analysis.HodgeTheory.Decomposition.CovectorSymbolAction.Constructions.twistedExteriorDerivative n J a x -
    ContinuousAlternatingMap.alternatizeUncurryFin ((lineConnectionTerm n (A x) (a x)).comp J)

theorem lineExteriorDerivative_covariant (n : ℕ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) (hΓ : ∀ v w, Γ x v w = Γ x w v) :
    lineExteriorDerivative n A a x =
      ContinuousAlternatingMap.alternatizeUncurryFin (lineCovectorConnectionDerivative n Γ A a x) := by
  unfold lineCovectorConnectionDerivative
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_add, Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative_alternation n Γ a x hΓ]
  rfl

theorem exteriorContraction_complex_smul (n : ℕ) (v : E) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1)) (c : ℂ) :
    Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n v (c • a) = c • Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n v a := by
  ext w
  rfl

variable [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

theorem lineTwistedExteriorDerivative_covariant (b : Module.Basis ι ℝ E) (n : ℕ)
    (J : E →L[ℝ] E) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E)
    (hΓ : ∀ v w, Γ x (J v) w = Γ x (J w) v) :
    lineTwistedExteriorDerivative n J A a x =
      -∑ i, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorDifferentialSymbol n ((b.coord i).toContinuousLinearMap.comp J)
        (lineCovectorConnectionDerivative n Γ A a x (b i)) := by
  rw [lineTwistedExteriorDerivative, Analysis.HodgeTheory.Decomposition.CovectorSymbolAction.Constructions.twistedExteriorDerivative_covariant b n J Γ a x hΓ,
    Analysis.HodgeTheory.Decomposition.CovectorSymbolAction.Constructions.alternation_comp_symbol_expansion b n]
  simp only [lineCovectorConnectionDerivative_apply, map_add, Finset.sum_add_distrib, neg_add_rev,
    lineConnectionTerm_apply]
  abel

end Linear

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype ι]

omit [IsScalarTower ℝ ℂ E] in
theorem metricLefschetzContraction_complex_smul (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) (c : ℂ) :
    Analysis.HodgeTheory.Decomposition.LefschetzSymbol.Constructions.metricLefschetzContraction n B b (c • a) = c • Analysis.HodgeTheory.Decomposition.LefschetzSymbol.Constructions.metricLefschetzContraction n B b a := by
  simp only [Analysis.HodgeTheory.Decomposition.LefschetzSymbol.Constructions.metricLefschetzContraction, _root_.smul_apply, Analysis.HodgeTheory.Decomposition.BivectorContraction.Constructions.bivectorContraction_apply,
    exteriorContraction_complex_smul, ← Finset.smul_sum]
  exact smul_comm (1 / 2 : ℝ) c _

def lineCovariantCodifferential (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1)) (x : E) : Analysis.DifferentialForms.Manifold.Basic.FormValue E n :=
  -∑ i, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap)
    (lineCovectorConnectionDerivative (n + 1) Γ A a x (b i))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionSymbols
