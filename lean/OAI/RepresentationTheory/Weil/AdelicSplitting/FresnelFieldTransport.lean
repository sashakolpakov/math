import OAI.RepresentationTheory.Weil.AdelicSplitting.FourierTransport
import OAI.RepresentationTheory.Weil.Local.NormalizedFresnel

/-! # Fresnel Field Transport -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.FresnelFieldTransport.LocalAnalysis

noncomputable section

/-! Exact transport of the Fourier-quadratic relation between local
field presentations, using the actual product measures. -/

open _root_.MeasureTheory

open OAI.RepresentationTheory.Weil.Local.NormalizedFresnel.Construction

variable {k l : Type} [NormedField k] [NormedField l]
  [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]
  [SecondCountableTopology k] [SecondCountableTopology l]

theorem fresnel_fieldTransport (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm)
    (N : ℕ) (ψ : AddChar k ℂ) (μ : Measure k) (ν : Measure l) [SigmaFinite ν]
    (hm : μ.map e = ν) (γ : ℂ)
    (hrel : ∀ (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat l N) (x : Local.FunctionsMetaplectic.Construction.Position l N),
      Local.FunctionsMetaplectic.Construction.fourierIntegral (ψ.compAddMonoidHom e.symm.toAddMonoidHom) (Measure.pi (fun _ : Fin N => ν))
        (Local.FunctionsMetaplectic.Construction.quadraticOperator (ψ.compAddMonoidHom e.symm.toAddMonoidHom) 1
          (Local.FunctionsMetaplectic.Construction.fourierIntegral (ψ.compAddMonoidHom e.symm.toAddMonoidHom) (Measure.pi (fun _ : Fin N => ν)) f.val)) x =
        γ * (ψ.compAddMonoidHom e.symm.toAddMonoidHom) (-Local.FunctionsMetaplectic.Construction.quadratic 1 x) *
          Local.FunctionsMetaplectic.Construction.fourierIntegral (ψ.compAddMonoidHom e.symm.toAddMonoidHom) (Measure.pi (fun _ : Fin N => ν))
            (Local.FunctionsMetaplectic.Construction.quadraticOperator (ψ.compAddMonoidHom e.symm.toAddMonoidHom) (-1) f.val) x)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (x : Local.FunctionsMetaplectic.Construction.Position k N) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin N => μ))
      (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ 1 (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin N => μ)) f.val)) x =
      γ * ψ (-Local.FunctionsMetaplectic.Construction.quadratic 1 x) *
        Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin N => μ)) (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ (-1) f.val) x := by
  let p := FieldTransport.LocalAnalysis.positionFieldEquiv N e he hi
  let ψ' := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  let T (f : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) := f ∘ p.symm
  let Fk := Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin N => μ))
  let Fl := Local.FunctionsMetaplectic.Construction.fourierIntegral ψ' (Measure.pi (fun _ : Fin N => ν))
  have hF (f : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) : T (Fk f) = Fl (T f) := by
    funext y
    have h := FourierTransport.LocalAnalysis.fourierIntegral_fieldTransport e he hi N ψ μ ν hm f (p.symm y)
    change Fl (T f) (p (p.symm y)) = Fk f (p.symm y) at h
    simpa only [p.apply_symm_apply] using! h.symm
  have hQ (B : Matrix (Fin N) (Fin N) k) (f : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) :
      T (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B f) = Local.FunctionsMetaplectic.Construction.quadraticOperator ψ' (B.map e) (T f) := by
    funext y
    change ψ (Local.FunctionsMetaplectic.Construction.quadratic B (p.symm y)) * f (p.symm y) =
      ψ (e.symm (Local.FunctionsMetaplectic.Construction.quadratic (B.map e) y)) * f (p.symm y)
    congr 1
    have h := FieldTransport.LocalAnalysis.quadratic_field_map e.symm.toRingHom (B.map e) y
    change Local.FunctionsMetaplectic.Construction.quadratic ((B.map e).map e.symm) (fun i => e.symm (y i)) =
      e.symm (Local.FunctionsMetaplectic.Construction.quadratic (B.map e) y) at h
    have hB : (B.map e).map e.symm = B := by ext i j; exact e.symm_apply_apply _
    rw [hB] at h
    exact congrArg ψ h
  have hQ1 (f : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) : T (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ 1 f) = Local.FunctionsMetaplectic.Construction.quadraticOperator ψ' 1 (T f) := by
    have hh := hQ 1 f
    have h1 : (1 : Matrix (Fin N) (Fin N) k).map e = 1 := e.toRingHom.mapMatrix.map_one
    rwa [h1] at hh
  have hQm (f : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) : T (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ (-1) f) = Local.FunctionsMetaplectic.Construction.quadraticOperator ψ' (-1) (T f) := by
    have hh := hQ (-1) f
    have h1 : (-1 : Matrix (Fin N) (Fin N) k).map e = -1 := by
      change e.toRingHom.mapMatrix (-1) = -1
      rw [map_neg, map_one]
    rwa [h1] at hh
  let f' : Local.FunctionsMetaplectic.Construction.schwartzBruhat l N := ⟨T f.val, FieldTransport.LocalAnalysis.schwartzBruhat_comp_fieldAddEquiv p.symm f.property⟩
  have h := hrel f' (p x)
  change Fl (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ' 1 (Fl (T f.val))) (p x) =
    γ * ψ' (-Local.FunctionsMetaplectic.Construction.quadratic 1 (p x)) * Fl (Local.FunctionsMetaplectic.Construction.quadraticOperator ψ' (-1) (T f.val)) (p x) at h
  rw [← hF, ← hQ1, ← hF, ← hQm, ← hF] at h
  have hphase : ψ' (-Local.FunctionsMetaplectic.Construction.quadratic 1 (p x)) = ψ (-Local.FunctionsMetaplectic.Construction.quadratic 1 x) := by
    change ψ (e.symm (-Local.FunctionsMetaplectic.Construction.quadratic 1 (fun i => e (x i)))) = _
    have hq := FieldTransport.LocalAnalysis.quadratic_field_map e.toRingHom (1 : Matrix (Fin N) (Fin N) k) x
    change Local.FunctionsMetaplectic.Construction.quadratic ((1 : Matrix (Fin N) (Fin N) k).map e) (fun i => e (x i)) =
      e (Local.FunctionsMetaplectic.Construction.quadratic 1 x) at hq
    have h1 : (1 : Matrix (Fin N) (Fin N) k).map e = 1 := e.toRingHom.mapMatrix.map_one
    rw [h1] at hq
    rw [hq, map_neg, e.symm_apply_apply]
  simpa only [T, Function.comp_apply, p.symm_apply_apply, hphase] using! h

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.FresnelFieldTransport.LocalAnalysis
