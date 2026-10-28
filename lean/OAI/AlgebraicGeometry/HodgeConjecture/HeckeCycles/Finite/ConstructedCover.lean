import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareKernelFin
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.OscillatorReindex

/-! # Constructed Cover -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ConstructedCover.CM.BareKernel

/-! Two-fold kernel exactness for the actual finite bare cover on any
finite index set, transported through actual coordinate relabeling. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FiniteOscillator.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe.CM.Group
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ReindexHeisenberg.CM.Pairing
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.OscillatorReindex.CM
variable {I : Type*} [Fintype I]

theorem kernel_sign (g : BareNe.CM.Group.BareGroup (I := I)) (hg : BareNe.CM.Group.bareProjection g = 1) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I, BareNe.CM.Group.bareAction g f = ε • f := by
  let e := Fintype.equivFin I
  have hp : BareNe.CM.Group.bareProjection (OscillatorReindex.CM.bareReindex e g) = 1 := by
    change FiniteOscillator.CM.projection (OscillatorReindex.CM.reindex e g.val) = 1
    have hg' : FiniteOscillator.CM.projection g.val = 1 := hg
    rw [OscillatorReindex.CM.projection_reindex, hg', map_one]
  obtain ⟨ε, hε, hf⟩ := BareKernelFin.CM.kernel_sign (Fintype.card I) (OscillatorReindex.CM.bareReindex e g) hp
  refine ⟨ε, hε, ?_⟩
  intro f
  apply (ReindexHeisenberg.CM.Pairing.testEquiv e).injective
  rw [map_smul]
  have hh := hf (ReindexHeisenberg.CM.Pairing.testEquiv e f)
  change FiniteOscillator.CM.action (OscillatorReindex.CM.reindex e g.val) (ReindexHeisenberg.CM.Pairing.testEquiv e f) = _ at hh
  rw [OscillatorReindex.CM.action_reindex] at hh
  exact hh

theorem kernel_exact (g : BareNe.CM.Group.BareGroup (I := I)) :
    BareNe.CM.Group.bareProjection g = 1 ↔ g = 1 ∨ g = BareNe.CM.Group.negOne := by
  constructor
  · intro hg
    obtain ⟨ε, hε, hf⟩ := kernel_sign g hg
    rcases sq_eq_one_iff.mp hε with rfl | rfl
    · left
      apply BareNe.CM.Group.faithful
      change (BareNe.CM.Group.bareProjection g, BareNe.CM.Group.bareAction g) = (BareNe.CM.Group.bareProjection 1, BareNe.CM.Group.bareAction 1)
      apply Prod.ext
      · rw [hg, map_one]
      · apply LinearEquiv.ext
        intro f
        rw [hf, one_smul, map_one]
        rfl
    · right
      apply BareNe.CM.Group.faithful
      change (BareNe.CM.Group.bareProjection g, BareNe.CM.Group.bareAction g) = (BareNe.CM.Group.bareProjection BareNe.CM.Group.negOne, BareNe.CM.Group.bareAction BareNe.CM.Group.negOne)
      apply Prod.ext
      · rw [hg, BareNe.CM.Group.project_negOne]
      · apply LinearEquiv.ext
        intro f
        rw [hf, BareNe.CM.Group.genuine]
        exact neg_one_smul ℂ f
  · rintro (rfl | rfl)
    · exact map_one _
    · exact BareNe.CM.Group.project_negOne

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ConstructedCover.CM.BareKernel

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ConstructedCover.CM

/-! The actual finite adelic Schrödinger cover: projection surjectivity,
exact two-element kernel, genuine action, and unitarity are all proved. -/

open scoped Classical
open _root_.MeasureTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe.CM.Group

def finiteCover (I : Type*) [Fintype I] [d : DecidableEq I] :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.SchrodingerCover RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf Constructed.AdelicCharacter.CM.Finite.character
      (Constructed.FiniteMeasure.CM.measure I) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (BareNe.CM.Group.BareGroup (I := I)) := by
  have hd : d = Classical.decEq I := Subsingleton.elim _ _
  cases hd
  exact {
    project := BareNe.CM.Group.bareProjection
    action := BareNe.CM.Group.bareAction
    surjective := BareBy.CM.Surjective.projection_surjective
    negOne := BareNe.CM.Group.negOne
    negOne_ne_one := BareNe.CM.Group.negOne_ne_one
    project_negOne := BareNe.CM.Group.project_negOne
    kernel := BareKernel.kernel_exact
    genuine := BareNe.CM.Group.genuine
    faithful := BareNe.CM.Group.faithful
    intertwines := BareNe.CM.Group.intertwines
    unitary := BareNe.CM.Group.unitary }

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ConstructedCover.CM

end

end OAI
