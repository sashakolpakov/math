import OAI.Analysis.HodgeTheory.Decomposition.MetricPullbackCurve
import OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential

/-! # Covector Symbol Action -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CovectorSymbolAction.Constructions

noncomputable section

section

/-! The induced infinitesimal covector action is a derivation of exterior
multiplication. This follows by differentiating the actual pullback identity. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def exteriorSymbolBilinear (n : ℕ) :
    (E →L[ℝ] ℝ) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1) :=
  ((ContinuousLinearMap.compL ℝ (DifferentialForms.Manifold.Basic.FormValue E n) (E →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n)
    (DifferentialForms.Manifold.Basic.FormValue E (n + 1))) (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ)).comp
      (ContinuousLinearMap.smulRightL ℝ E (DifferentialForms.Manifold.Basic.FormValue E n))

theorem exteriorSymbolBilinear_apply (n : ℕ) (ξ : E →L[ℝ] ℝ) (a : DifferentialForms.Manifold.Basic.FormValue E n) :
    exteriorSymbolBilinear n ξ a = SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ a := rfl

theorem covectorPerturbation_hasDerivAt (A : E →L[ℝ] E) (ξ : E →L[ℝ] ℝ) :
    HasDerivAt (fun t => ξ.comp (MetricPullbackCurve.Constructions.tangentLinearPerturbation A t)) (ξ.comp A) 0 := by
  exact ((ContinuousLinearMap.compL ℝ E E ℝ) ξ).hasFDerivAt.comp_hasDerivAt
    0 (MetricPullbackCurve.Constructions.tangentLinearPerturbation_hasDerivAt A)

theorem exteriorSymbol_hasDerivAt (n : ℕ) (ξ : ℝ → E →L[ℝ] ℝ) (a : ℝ → DifferentialForms.Manifold.Basic.FormValue E n)
    (dξ : E →L[ℝ] ℝ) (da : DifferentialForms.Manifold.Basic.FormValue E n) (t : ℝ)
    (hξ : HasDerivAt ξ dξ t) (ha : HasDerivAt a da t) :
    HasDerivAt (fun s => SymbolDifferential.Constructions.exteriorDifferentialSymbol n (ξ s) (a s))
      (SymbolDifferential.Constructions.exteriorDifferentialSymbol n (ξ t) da + SymbolDifferential.Constructions.exteriorDifferentialSymbol n dξ (a t)) t := by
  let L := exteriorSymbolBilinear (E := E) n
  have hF : HasFDerivAt L L (ξ t) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := E →L[ℝ] ℝ)
      (F := DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1)) L
  have hL : HasDerivAt (fun s => L (ξ s)) (L dξ) t := by
    convert! HasFDerivAt.comp_hasDerivAt (F := E →L[ℝ] ℝ)
      (E := DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1)) t hF hξ using 1
  convert! hL.clm_apply ha using 1
  exact add_comm _ _

theorem covectorInfinitesimalAction_exteriorSymbol (n : ℕ) (A : E →L[ℝ] E)
    (ξ : E →L[ℝ] ℝ) (a : DifferentialForms.Manifold.Basic.FormValue E n) :
    CovectorConnection.Constructions.covectorInfinitesimalAction (n + 1) A (SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ a) =
      SymbolDifferential.Constructions.exteriorDifferentialSymbol n (ξ.comp A) a +
        SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ (CovectorConnection.Constructions.covectorInfinitesimalAction n A a) := by
  have hbil := exteriorSymbol_hasDerivAt n _ _ _ _ 0
    (covectorPerturbation_hasDerivAt A ξ) (MetricPullbackCurve.Constructions.covectorPullback_hasDerivAt n A a)
  have hleft := MetricPullbackCurve.Constructions.covectorPullback_hasDerivAt (n + 1) A (SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ a)
  have heq : (fun t => (SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ a).compContinuousLinearMap (MetricPullbackCurve.Constructions.tangentLinearPerturbation A t)) =
      (fun t => exteriorSymbolBilinear n (ξ.comp (MetricPullbackCurve.Constructions.tangentLinearPerturbation A t))
        (a.compContinuousLinearMap (MetricPullbackCurve.Constructions.tangentLinearPerturbation A t))) := by
    funext t
    exact SymbolDifferential.Constructions.exteriorDifferentialSymbol_pullback n _ ξ a
  rw [heq] at hleft
  have h := hleft.unique hbil
  have ha : a.compContinuousLinearMap (ContinuousLinearMap.id ℝ E) = a := by ext v; rfl
  simpa only [MetricPullbackCurve.Constructions.tangentLinearPerturbation_zero, ContinuousLinearMap.comp_id, ha,
    ContinuousLinearMap.comp_apply, exteriorSymbolBilinear_apply, add_comm] using h

end

/-! The constant-complex-structure twist of the genuine exterior derivative,
with its exact covariant principal-symbol expansion. -/

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι]

theorem alternation_comp_symbol_expansion (b : Module.Basis ι ℝ E) (n : ℕ)
    (L : E →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n) (J : E →L[ℝ] E) :
    ContinuousAlternatingMap.alternatizeUncurryFin (L.comp J) =
      ∑ i, SymbolDifferential.Constructions.exteriorDifferentialSymbol n ((b.coord i).toContinuousLinearMap.comp J) (L (b i)) := by
  have hc : L.comp J = ∑ i, ((b.coord i).toContinuousLinearMap.comp J).smulRight (L (b i)) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]
    have h := congrArg (fun K : E →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n => K (J v)) (SymbolDifferential.Constructions.derivative_basis_expansion b n L)
    simpa only [sum_apply, ContinuousLinearMap.smulRight_apply] using h
  change ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ (L.comp J) = _
  rw [hc, map_sum]
  rfl

omit [FiniteDimensional ℝ E] [Fintype ι] in
def twistedExteriorDerivative (n : ℕ) (J : E →L[ℝ] E) (a : E → DifferentialForms.Manifold.Basic.FormValue E n) (x : E) :
    DifferentialForms.Manifold.Basic.FormValue E (n + 1) :=
  -ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ a x).comp J)

theorem twistedExteriorDerivative_symbol (b : Module.Basis ι ℝ E) (n : ℕ)
    (J : E →L[ℝ] E) (a : E → DifferentialForms.Manifold.Basic.FormValue E n) (x : E) :
    twistedExteriorDerivative n J a x =
      -∑ i, SymbolDifferential.Constructions.exteriorDifferentialSymbol n ((b.coord i).toContinuousLinearMap.comp J) (fderiv ℝ a x (b i)) := by
  rw [twistedExteriorDerivative, alternation_comp_symbol_expansion b n]

theorem twistedExteriorDerivative_covariant (b : Module.Basis ι ℝ E) (n : ℕ)
    (J : E →L[ℝ] E) (Γ : E → E →L[ℝ] E →L[ℝ] E) (a : E → DifferentialForms.Manifold.Basic.FormValue E n) (x : E)
    (hΓJ : ∀ u v, Γ x (J u) v = Γ x (J v) u) :
    twistedExteriorDerivative n J a x =
      -∑ i, SymbolDifferential.Constructions.exteriorDifferentialSymbol n ((b.coord i).toContinuousLinearMap.comp J)
        (CovectorConnection.Constructions.covectorConnectionDerivative n Γ a x (b i)) := by
  have hz := ContinuousAlternatingMap.alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero
    (a x) (ContinuousLinearMap.id ℝ E) (show ∀ u v, (Γ x).comp J u v = (Γ x).comp J v u from hΓJ)
  have heq : ((a x).fderivCompContinuousLinearMap (ContinuousLinearMap.id ℝ E)).comp ((Γ x).comp J) =
      (((a x).fderivCompContinuousLinearMap (ContinuousLinearMap.id ℝ E)).comp (Γ x)).comp J := rfl
  rw [heq, alternation_comp_symbol_expansion b n] at hz
  rw [twistedExteriorDerivative_symbol b n]
  simp only [CovectorConnection.Constructions.covectorConnectionDerivative_apply, map_sub, Finset.sum_sub_distrib]
  change -(∑ i, SymbolDifferential.Constructions.exteriorDifferentialSymbol n ((b.coord i).toContinuousLinearMap.comp J) (fderiv ℝ a x (b i))) =
    -((∑ i, SymbolDifferential.Constructions.exteriorDifferentialSymbol n ((b.coord i).toContinuousLinearMap.comp J) (fderiv ℝ a x (b i))) -
      ∑ i, SymbolDifferential.Constructions.exteriorDifferentialSymbol n ((b.coord i).toContinuousLinearMap.comp J)
        (((a x).fderivCompContinuousLinearMap (ContinuousLinearMap.id ℝ E)).comp (Γ x) (b i)))
  rw [hz, sub_zero]

end

end OAI.Analysis.HodgeTheory.Decomposition.CovectorSymbolAction.Constructions
