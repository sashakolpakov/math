import Mathlib

/-! # Equivalence Sites -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.EquivalenceSites

noncomputable section

/-!
# Equivalences preserving generating coverings

An equivalence that preserves the specified covering families preserves
their generated topology. Preservation in both directions supplies the
continuous and cocontinuous functors used for exact restriction of sheaves.
-/

open _root_.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (e : C ≌ D) (J : Precoverage C) (K : Precoverage D)

theorem coverPreserving (h : J ≤ K.comap e.functor) :
    CoverPreserving J.toGrothendieck K.toGrothendieck e.functor := by
  have hle : J.toGrothendieck ≤ e.functor.restrictedTopology K.toGrothendieck :=
    (Precoverage.toGrothendieck_mono h).trans
      (Precoverage.toGrothendieck_comap_le_restrictedTopology (F := e.functor) K)
  constructor
  intro U S hS
  exact Functor.mem_restrictedTopology_iff.mp (hle _ hS)

theorem continuous (h : J ≤ K.comap e.functor) :
    e.functor.IsContinuous J.toGrothendieck K.toGrothendieck :=
  Functor.isContinuous_iff_coverPreserving.mpr (coverPreserving e J K h)

theorem cocontinuous (h : K ≤ J.comap e.inverse) :
    e.functor.IsCocontinuous J.toGrothendieck K.toGrothendieck :=
  (e.toAdjunction.isCocontinuous_iff_coverPreserving J.toGrothendieck K.toGrothendieck).mpr
    (coverPreserving e.symm K J h)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.EquivalenceSites
