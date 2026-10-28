import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ReindexHeisenberg
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe
import OAI.RepresentationTheory.Hecke.RadialDilation.TensorCommutant

/-! # Oscillator Reindex -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.OscillatorReindex.CM

noncomputable section

/-! Coordinate relabeling transports the actual oscillator group and
its intrinsic bare subgroup, including the distinguished negative identity. -/

open scoped Classical _root_.Matrix commutatorElement
open _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe.CM.Group
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ReindexHeisenberg.CM.Pairing
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ReindexHeisenberg.CM
variable {I J : Type*} [Fintype I] [Fintype J]

def reindex (e : I ≃ J) : FiniteOscillator.CM.Oscillator (I := I) →* FiniteOscillator.CM.Oscillator (I := J) where
  toFun g := ⟨(RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e (FiniteOscillator.CM.projection g), RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.conjugateLinearAut (ReindexHeisenberg.CM.Pairing.testEquiv e) (FiniteOscillator.CM.action g)), by
    constructor
    · exact ReindexHeisenberg.CM.Pairing.transport_unitary e (FiniteOscillator.CM.action g) (FiniteOscillator.CM.unitary g)
    · intro v f h
      change FiniteOscillator.CM.graph v f h ↔ FiniteOscillator.CM.graph (FiniteOscillator.CM.phaseAction (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e (FiniteOscillator.CM.projection g)) v)
        (ReindexHeisenberg.CM.Pairing.testEquiv e (FiniteOscillator.CM.action g ((ReindexHeisenberg.CM.Pairing.testEquiv e).symm f))) (ReindexHeisenberg.CM.Pairing.testEquiv e (FiniteOscillator.CM.action g ((ReindexHeisenberg.CM.Pairing.testEquiv e).symm h)))
      calc
        FiniteOscillator.CM.graph v f h ↔ FiniteOscillator.CM.graph (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex (e.symm.sumCongr e.symm) v)
            (ReindexHeisenberg.CM.Pairing.testEquiv e.symm f) (ReindexHeisenberg.CM.Pairing.testEquiv e.symm h) := ReindexHeisenberg.CM.graph_reindex e.symm v f h
        _ ↔ FiniteOscillator.CM.graph (FiniteOscillator.CM.phaseAction (FiniteOscillator.CM.projection g) (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex (e.symm.sumCongr e.symm) v))
            (FiniteOscillator.CM.action g (ReindexHeisenberg.CM.Pairing.testEquiv e.symm f)) (FiniteOscillator.CM.action g (ReindexHeisenberg.CM.Pairing.testEquiv e.symm h)) := g.property.2 _ _ _
        _ ↔ FiniteOscillator.CM.graph (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex (e.sumCongr e)
              (FiniteOscillator.CM.phaseAction (FiniteOscillator.CM.projection g) (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex (e.symm.sumCongr e.symm) v)))
            (ReindexHeisenberg.CM.Pairing.testEquiv e (FiniteOscillator.CM.action g (ReindexHeisenberg.CM.Pairing.testEquiv e.symm f)))
            (ReindexHeisenberg.CM.Pairing.testEquiv e (FiniteOscillator.CM.action g (ReindexHeisenberg.CM.Pairing.testEquiv e.symm h))) := ReindexHeisenberg.CM.graph_reindex e _ _ _
        _ ↔ _ := by rw [ReindexHeisenberg.CM.phase_reindex_inverse]; rfl⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · exact (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e).map_one
    · exact (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.conjugateLinearAut (ReindexHeisenberg.CM.Pairing.testEquiv e)).map_one
  map_mul' g h := by
    apply Subtype.ext
    apply Prod.ext
    · exact (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e).map_mul (FiniteOscillator.CM.projection g) (FiniteOscillator.CM.projection h)
    · exact (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.conjugateLinearAut (ReindexHeisenberg.CM.Pairing.testEquiv e)).map_mul (FiniteOscillator.CM.action g) (FiniteOscillator.CM.action h)

theorem projection_reindex (e : I ≃ J) (g : FiniteOscillator.CM.Oscillator (I := I)) :
    FiniteOscillator.CM.projection (reindex e g) = RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e (FiniteOscillator.CM.projection g) := rfl

theorem action_reindex (e : I ≃ J) (g : FiniteOscillator.CM.Oscillator (I := I)) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    FiniteOscillator.CM.action (reindex e g) (ReindexHeisenberg.CM.Pairing.testEquiv e f) = ReindexHeisenberg.CM.Pairing.testEquiv e (FiniteOscillator.CM.action g f) := by
  change ReindexHeisenberg.CM.Pairing.testEquiv e (FiniteOscillator.CM.action g ((ReindexHeisenberg.CM.Pairing.testEquiv e).symm (ReindexHeisenberg.CM.Pairing.testEquiv e f))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem reindex_minus (e : I ≃ J) : reindex e BareNe.CM.Group.minus = BareNe.CM.Group.minus := by
  apply Subtype.ext
  apply Prod.ext
  · exact (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e).map_one
  · exact RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.conjugateLinearAut_neg (ReindexHeisenberg.CM.Pairing.testEquiv e)

theorem reindex_bare (e : I ≃ J) (g : FiniteOscillator.CM.Oscillator (I := I)) (hg : g ∈ BareNe.CM.Group.bareSubgroup) :
    reindex e g ∈ BareNe.CM.Group.bareSubgroup := by
  have hh : BareNe.CM.Group.bareSubgroup (I := I) ≤ (BareNe.CM.Group.bareSubgroup (I := J)).comap (reindex e) := by
    rw [BareNe.CM.Group.bareSubgroup, Subgroup.closure_le]
    intro u hu
    rcases hu with ⟨a, b, rfl⟩ | rfl
    · change reindex e ⁅a, b⁆ ∈ BareNe.CM.Group.bareSubgroup
      rw [map_commutatorElement]
      exact Subgroup.subset_closure (Or.inl ⟨reindex e a, reindex e b, rfl⟩)
    · change reindex e BareNe.CM.Group.minus ∈ BareNe.CM.Group.bareSubgroup
      rw [reindex_minus]
      exact BareNe.CM.Group.negOne.property
  exact hh hg

def bareReindex (e : I ≃ J) : BareNe.CM.Group.BareGroup (I := I) →* BareNe.CM.Group.BareGroup (I := J) where
  toFun g := ⟨reindex e g.val, reindex_bare e g.val g.property⟩
  map_one' := Subtype.ext (reindex e).map_one
  map_mul' g h := Subtype.ext ((reindex e).map_mul g.val h.val)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.OscillatorReindex.CM
