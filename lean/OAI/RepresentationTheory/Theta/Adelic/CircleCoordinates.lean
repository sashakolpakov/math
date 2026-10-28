import OAI.RepresentationTheory.Weil.UnitarySplitting.FrameTransport
import OAI.RepresentationTheory.Weil.AdelicSplitting.SchrodingerPairing

/-! # Circle Coordinates -/

namespace OAI.RepresentationTheory.Theta.Adelic.CircleCoordinates

noncomputable section

/-! Transport UnitarySplitting's actual trace-tensor intertwiners into AdelicSplitting's matrix
oscillator group, preserving the operator and the strong topology. -/

open OAI.RepresentationTheory.Weil.UnitarySplitting.FrameTransport.Construction OAI.RepresentationTheory.Weil.AdelicSplitting.SchrodingerPairing.Construction

variable {k E : Type} [NormedField k] [NormedField E] [Algebra k E] {n m : ℕ}
variable (σ : E ≃ₐ[k] E) (H : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin m) (Fin m) E)
variable (c : Weil.UnitarySplitting.Oscillator.Construction.SymplecticFrame σ H K)

def coordinateLinear (g : Weil.UnitarySplitting.Oscillator.Construction.TensorSymplectic σ H K) : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k (n * m) ≃ₗ[k] Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k (n * m) :=
  c.coordinates.symm.trans (g.val.trans c.coordinates)

theorem coordinateLinear_preserves (g : Weil.UnitarySplitting.Oscillator.Construction.TensorSymplectic σ H K) (x y : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k (n * m)) :
    Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerPairing k (n * m) (coordinateLinear σ H K c g x) (coordinateLinear σ H K c g y) =
      Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerPairing k (n * m) x y := by
  simp only [Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerPairing_eq_standard]
  change Weil.UnitarySplitting.Oscillator.Construction.standardSymplecticPairing (n * m)
    (c.coordinates (g.val (c.coordinates.symm x))) (c.coordinates (g.val (c.coordinates.symm y))) = _
  rw [c.preserves, g.property, ← c.preserves, c.coordinates.apply_symm_apply, c.coordinates.apply_symm_apply]

def coordinateSymplectic : Weil.UnitarySplitting.Oscillator.Construction.TensorSymplectic σ H K →* Weil.Local.FunctionsMetaplectic.Construction.Symplectic k (n * m) where
  toFun g := ⟨LinearMap.toMatrix' (coordinateLinear σ H K c g).toLinearMap, by
    apply SymplecticGroup.mem_iff'.mpr
    apply Matrix.toBilin'.injective
    rw [← Matrix.toBilin'_comp]
    simp only [Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact coordinateLinear_preserves σ H K c g x y⟩
  map_one' := by
    apply Subtype.ext
    apply LinearMap.toMatrix'.symm.injective
    ext x i
    simp [coordinateLinear]
  map_mul' g h := by
    apply Subtype.ext
    apply LinearMap.toMatrix'.symm.injective
    ext x i
    simp [coordinateLinear]

theorem coordinateSymplectic_apply (g : Weil.UnitarySplitting.Oscillator.Construction.TensorSymplectic σ H K) (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k (n * m)) :
    Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (coordinateSymplectic σ H K c g) v =
      c.coordinates (g.val (c.coordinates.symm v)) := by
  change Matrix.toLin' (LinearMap.toMatrix' (coordinateLinear σ H K c g).toLinearMap) v = _
  rw [Matrix.toLin'_toMatrix']
  rfl

theorem coordinateSymplectic_continuous (hc : Continuous c.coordinates) :
    Continuous (coordinateSymplectic σ H K c) := by
  have ho : Continuous (fun g : Weil.UnitarySplitting.Oscillator.Construction.TensorSymplectic σ H K =>
      ((fun x => g.val x), (fun x => g.val.symm x))) := continuous_induced_dom
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun g : Weil.UnitarySplitting.Oscillator.Construction.TensorSymplectic σ H K =>
    (LinearMap.toMatrix' (coordinateLinear σ H K c g).toLinearMap) i j)
  simp only [LinearMap.toMatrix'_apply]
  exact (continuous_apply i).comp (hc.comp
    ((continuous_apply (c.coordinates.symm (Pi.single j 1))).comp (continuous_fst.comp ho)))

variable [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k ℂ)

def coordinateCover : Weil.UnitarySplitting.Oscillator.Construction.CircleExtension σ H K c ψ →* Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ where
  toFun a := ⟨(coordinateSymplectic σ H K c a.val.1, a.val.2), a.property.1, by
    intro v f h
    have he := a.property.2 (c.coordinates.symm v) f h
    rw [c.coordinates.apply_symm_apply] at he
    rw [coordinateSymplectic_apply]
    exact he⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_one (coordinateSymplectic σ H K c)
    · rfl
  map_mul' a b := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_mul (coordinateSymplectic σ H K c) a.val.1 b.val.1
    · rfl

theorem coordinateCover_operator (a : Weil.UnitarySplitting.Oscillator.Construction.CircleExtension σ H K c ψ) :
    Weil.AdelicSplitting.Oscillator.Construction.localOperator k (n * m) ψ (coordinateCover σ H K c ψ a) = a.val.2 := rfl

theorem coordinateCover_continuous (hc : Continuous c.coordinates) :
    Continuous (coordinateCover σ H K c ψ) := by
  have ho : Continuous (Weil.UnitarySplitting.Oscillator.Construction.oscillatorObservations σ H K c ψ) := continuous_induced_dom
  apply continuous_induced_rng.mpr
  exact ((coordinateSymplectic_continuous σ H K c hc).comp (continuous_fst.comp ho)).prodMk
    (continuous_snd.comp ho)

def coordinateCoverContinuous (hc : Continuous c.coordinates) :
    Weil.UnitarySplitting.Oscillator.Construction.CircleExtension σ H K c ψ →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ :=
  ⟨coordinateCover σ H K c ψ, coordinateCover_continuous σ H K c ψ hc⟩

end

end OAI.RepresentationTheory.Theta.Adelic.CircleCoordinates
