import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.UnitaryTransport
import OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex

/-! # Reindex Heisenberg -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ReindexHeisenberg.CM.Pairing

/-! Actual finite-coordinate relabeling on adelic Schwartz functions.
The Haar pairing changes by a proved positive scalar, which suffices to
transport unitary oscillator actions. -/

open scoped Classical
open _root_.MeasureTheory
open OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM
variable {I J : Type*} [Fintype I] [Fintype J]

def coordinateEquiv (e : I ≃ J) : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ≃L[RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf] (J → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) where
  toFun x := RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e x
  invFun y := RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm y
  left_inv x := by funext i; exact congrArg x (e.symm_apply_apply i)
  right_inv y := by funext j; exact congrArg y (e.apply_symm_apply j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e).continuous
  continuous_invFun := (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm).continuous

def testEquiv (e : I ≃ J) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz J where
  toFun f := ⟨f.val ∘ RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm, (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mpr
    ⟨((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mp f.property).1.comp_continuous (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm).continuous,
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_hasCompactSupport f).comp_homeomorph (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm)⟩⟩
  invFun f := ⟨f.val ∘ RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e, (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mpr
    ⟨((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mp f.property).1.comp_continuous (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e).continuous,
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_hasCompactSupport f).comp_homeomorph (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e)⟩⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    change f.val (fun i => x (e.symm (e i))) = f.val x
    simp only [e.symm_apply_apply]
  right_inv f := by
    apply Subtype.ext
    funext y
    change f.val (fun j => y (e (e.symm j))) = f.val y
    simp only [e.apply_symm_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem testEquiv_apply (e : I ≃ J) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (y : J → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    (testEquiv e f).val y = f.val (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm y) := rfl

def factor (e : I ≃ J) : NNReal :=
  Measure.addHaarScalarFactor ((Constructed.FiniteMeasure.CM.measure J).map (coordinateEquiv e.symm)) (Constructed.FiniteMeasure.CM.measure I)

theorem factor_pos (e : I ≃ J) : 0 < factor e :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

theorem pairing (e : I ≃ J) (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    FiniteOscillator.CM.integralPairing (testEquiv e f) (testEquiv e h) = (factor e : ℂ) * FiniteOscillator.CM.integralPairing f h := by
  have hm := (coordinateEquiv e.symm).toHomeomorph.isClosedEmbedding.integral_map
    (μ := Constructed.FiniteMeasure.CM.measure J) (fun x => f.val x * star (h.val x))
  change (∫ x, f.val x * star (h.val x) ∂((Constructed.FiniteMeasure.CM.measure J).map (coordinateEquiv e.symm))) =
    ∫ x, f.val (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm x) * star (h.val (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm x)) ∂(Constructed.FiniteMeasure.CM.measure J) at hm
  change (∫ x, f.val (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm x) * star (h.val (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm x)) ∂(Constructed.FiniteMeasure.CM.measure J)) = _
  rw [← hm, Measure.isAddLeftInvariant_eq_smul ((Constructed.FiniteMeasure.CM.measure J).map (coordinateEquiv e.symm)) (Constructed.FiniteMeasure.CM.measure I),
    integral_smul_nnreal_measure]
  rfl

theorem transport_unitary (e : I ≃ J) (U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
    (hU : ∀ f h, FiniteOscillator.CM.integralPairing (U f) (U h) = FiniteOscillator.CM.integralPairing f h)
    (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz J) :
    FiniteOscillator.CM.integralPairing (testEquiv e (U ((testEquiv e).symm f)))
      (testEquiv e (U ((testEquiv e).symm h))) = FiniteOscillator.CM.integralPairing f h := by
  rw [pairing, hU, ← pairing, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ReindexHeisenberg.CM.Pairing

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ReindexHeisenberg.CM

/-! Actual finite Heisenberg operators and their graphs commute with
coordinate relabeling. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ReindexHeisenberg.CM.Pairing
variable {I J : Type*} [Fintype I] [Fintype J]

theorem heisenberg_reindex (e : I ≃ J) (p q : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    Pairing.testEquiv e (FourierHeisenberg.CM.operator p q f) =
      FourierHeisenberg.CM.operator (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e p) (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e q) (Pairing.testEquiv e f) := by
  apply Subtype.ext
  funext y
  exact RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.heisenberg_positionReindex e Constructed.AdelicCharacter.CM.Finite.character p q f.val y

theorem graph_eq (v : FiniteOscillator.CM.Phase (I := I)) (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    FiniteOscillator.CM.graph v f h ↔ h = FourierHeisenberg.CM.operator
      (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) f := by
  constructor
  · intro hh
    exact Subtype.ext hh
  · intro hh
    exact congrArg Subtype.val hh

theorem graph_reindex (e : I ≃ J) (v : FiniteOscillator.CM.Phase (I := I)) (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    FiniteOscillator.CM.graph v f h ↔ FiniteOscillator.CM.graph (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex (e.sumCongr e) v) (Pairing.testEquiv e f) (Pairing.testEquiv e h) := by
  rw [graph_eq, graph_eq]
  change h = FourierHeisenberg.CM.operator _ _ f ↔
    Pairing.testEquiv e h = FourierHeisenberg.CM.operator
      (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e (fun i => v (Sum.inl i)))
      (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e (fun i => v (Sum.inr i))) (Pairing.testEquiv e f)
  rw [← heisenberg_reindex]
  exact (Pairing.testEquiv e).injective.eq_iff.symm

theorem phase_reindex_inverse (e : I ≃ J) (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : FiniteOscillator.CM.Phase (I := J)) :
    RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex (e.sumCongr e) (FiniteOscillator.CM.phaseAction g (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex (e.symm.sumCongr e.symm) v)) =
      FiniteOscillator.CM.phaseAction (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e g) v := by
  have h := RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex_action e g (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex (e.symm.sumCongr e.symm) v)
  have hv : RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex (e.sumCongr e) (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex (e.symm.sumCongr e.symm) v) = v := by
    funext i
    cases i <;> simp [RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex]
  rw [hv] at h
  exact h.symm

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ReindexHeisenberg.CM

end

end OAI
