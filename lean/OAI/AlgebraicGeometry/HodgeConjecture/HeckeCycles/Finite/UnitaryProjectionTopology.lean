import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.UnitarySymplectic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticTopology

/-! # Unitary Projection Topology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.UnitaryProjectionTopology.CM

noncomputable section

/-! The actual finite unitary symplectic projection is continuous. Local
continuity follows from the supplied continuous oscillator splittings. -/

open scoped Classical _root_.NumberField
open Filter
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

variable (F : Type) [Field F] [NumberField F] (d : F) (n m : ℕ)
  (H : (Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
  (K : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
  (hd : d ≠ 0) (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d n m H K)
  (D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d n m H K hd C P)

include D in
theorem local_continuous (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    Continuous (UnitarySymplectic.CM.localHom F d n m H K P v) := by
  let : MeasurableSpace (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) := RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionMeasurableSpace F (.inr v)
  let : BorelSpace (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) := RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionBorelSpace F (.inr v)
  have hc := (RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localProjection_continuous (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (n * m)
    (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F C.ψ (.inr v))).comp
      (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUSplitting F H K hd C P D (.inr v)).continuous
  exact hc.congr (fun g => D.covers (.inr v) (RepresentationTheory.Theta.Adelic.FiniteSchwartz.localSUToPair F H K (.inr v) g))

theorem restricted_continuous :
    Continuous (UnitarySymplectic.CM.restricted F d n m H K hd C P D) :=
  (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.restrictedContinuousMap (fun v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F =>
    RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr v))
      (fun v => RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.symplecticIntegral F (n * m) (.inr v))
      (fun v => ⟨UnitarySymplectic.CM.localHom F d n m H K P v,
        local_continuous F d n m H K hd C P D v⟩)
      (UnitarySymplectic.CM.local_integral F d n m H K hd C P D)).continuous

theorem assembled_matrix : Continuous (fun g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H =>
    (UnitarySymplectic.CM.assembled F d n m H K hd C P D g).val) :=
  (SymplecticTopology.CM.assembled_matrix F (n * m)).comp
    (restricted_continuous F d n m H K hd C P D)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.UnitaryProjectionTopology.CM
