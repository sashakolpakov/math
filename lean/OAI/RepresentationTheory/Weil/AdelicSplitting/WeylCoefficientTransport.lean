import OAI.RepresentationTheory.Weil.AdelicSplitting.PhaseMeasure
import OAI.RepresentationTheory.Weil.AdelicSplitting.FieldTransport

/-! # Weyl Coefficient Transport -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.WeylCoefficientTransport.Construction

noncomputable section

/-! Weyl coefficients in ordinary position coordinates and exact field
transport with the pushed-forward Haar measure. -/

open _root_.MeasureTheory

open OAI.RepresentationTheory.Weil.AdelicSplitting.FieldTransport.LocalAnalysis

variable {k : Type} [NormedField k] [MeasurableSpace k] {N : ℕ}

def positionWeylCoefficient (ψ : AddChar k ℂ) (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k N))
    (f h : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position k (N + N)) : ℂ :=
  UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ μ f h ((PhaseMeasure.Construction.phaseCoordinates k N).symm x)

variable [BorelSpace k] [SecondCountableTopology k]
  {l : Type} [NormedField l] [MeasurableSpace l] [BorelSpace l] [SecondCountableTopology l]

theorem positionWeylCoefficient_fieldTransport (e : k ≃+* l)
    (he : Continuous e) (hi : Continuous e.symm) (ψ : AddChar k ℂ)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k N)) (f h : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position k (N + N)) :
    positionWeylCoefficient (ψ.compAddMonoidHom e.symm.toAddMonoidHom)
      (μ.map (FieldTransport.LocalAnalysis.positionFieldEquiv N e he hi))
      (f ∘ (FieldTransport.LocalAnalysis.positionFieldEquiv N e he hi).symm) (h ∘ (FieldTransport.LocalAnalysis.positionFieldEquiv N e he hi).symm)
      (FieldTransport.LocalAnalysis.positionFieldEquiv (N + N) e he hi x) = positionWeylCoefficient ψ μ f h x := by
  let p := FieldTransport.LocalAnalysis.positionFieldEquiv N e he hi
  let em := p.toHomeomorph.toMeasurableEquiv
  unfold positionWeylCoefficient UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient
  rw [show μ.map (FieldTransport.LocalAnalysis.positionFieldEquiv N e he hi) = μ.map em from rfl, integral_map_equiv]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change ψ (e.symm (∑ i, e (((PhaseMeasure.Construction.phaseCoordinates k N).symm x) (.inr i)) *
      (e (y i) - e (((PhaseMeasure.Construction.phaseCoordinates k N).symm x) (.inl i)) / 2))) *
      f (p.symm (fun i => e (y i) - e (((PhaseMeasure.Construction.phaseCoordinates k N).symm x) (.inl i)))) *
        star (h (p.symm (p y))) = _
    rw [p.symm_apply_apply]
    have hq : (fun i => e (y i) - e (((PhaseMeasure.Construction.phaseCoordinates k N).symm x) (.inl i))) =
        p (fun i => y i - ((PhaseMeasure.Construction.phaseCoordinates k N).symm x) (.inl i)) := by
      funext i
      exact (map_sub e _ _).symm
    rw [hq, p.symm_apply_apply]
    have ht : (∑ i, e (((PhaseMeasure.Construction.phaseCoordinates k N).symm x) (.inr i)) *
        (e (y i) - e (((PhaseMeasure.Construction.phaseCoordinates k N).symm x) (.inl i)) / 2)) =
        e (∑ i, ((PhaseMeasure.Construction.phaseCoordinates k N).symm x) (.inr i) *
          (y i - ((PhaseMeasure.Construction.phaseCoordinates k N).symm x) (.inl i) / 2)) := by
      simp only [map_sum, map_mul, map_sub, map_div₀, map_ofNat]
    rw [ht, e.symm_apply_apply]
    rfl

theorem positionWeylCoefficient_mem_fieldTransport (e : k ≃+* l)
    (he : Continuous e) (hi : Continuous e.symm) (ψ : AddChar k ℂ)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k N)) [μ.IsAddHaarMeasure]
    (hm : ∀ (ν : Measure (Local.FunctionsMetaplectic.Construction.Position l N)) [ν.IsAddHaarMeasure] (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat l N),
      positionWeylCoefficient (ψ.compAddMonoidHom e.symm.toAddMonoidHom) ν f.val h.val ∈
        Local.FunctionsMetaplectic.Construction.schwartzBruhat l (N + N))
    (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    positionWeylCoefficient ψ μ f.val h.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k (N + N) := by
  let p := FieldTransport.LocalAnalysis.positionFieldEquiv N e he hi
  let ν := μ.map p
  let : ν.IsAddHaarMeasure := p.isAddHaarMeasure_map μ
  let f' : Local.FunctionsMetaplectic.Construction.schwartzBruhat l N := ⟨f.val ∘ p.symm, FieldTransport.LocalAnalysis.schwartzBruhat_comp_fieldAddEquiv p.symm f.property⟩
  let h' : Local.FunctionsMetaplectic.Construction.schwartzBruhat l N := ⟨h.val ∘ p.symm, FieldTransport.LocalAnalysis.schwartzBruhat_comp_fieldAddEquiv p.symm h.property⟩
  have hh := FieldTransport.LocalAnalysis.schwartzBruhat_comp_fieldAddEquiv (FieldTransport.LocalAnalysis.positionFieldEquiv (N + N) e he hi) (hm ν f' h')
  convert hh using 1
  funext x
  exact (positionWeylCoefficient_fieldTransport e he hi ψ μ f.val h.val x).symm

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.WeylCoefficientTransport.Construction
