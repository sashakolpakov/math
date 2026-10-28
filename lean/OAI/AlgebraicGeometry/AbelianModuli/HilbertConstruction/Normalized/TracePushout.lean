import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Free.AlgebraTraceBaseChange
import Mathlib.Algebra.Category.Ring.Constructions

/-! # Trace Pushout -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.TracePushout

noncomputable section

/-! Normalized traces are compatible with categorical pushout squares of commutative rings. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u

variable {R A S B : Type u} [CommRing R] [CommRing A] [CommRing S] [CommRing B]
variable [Algebra R A] [Algebra R S] [Algebra A B] [Algebra S B] [Algebra R B]
variable [IsScalarTower R S B] [IsScalarTower R A B]

theorem normalizedAlgebraTrace_of_isPushout {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R A)
    (h : IsPushout (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap S B))
      (CommRingCat.ofHom (algebraMap A B))) (u : Rˣ) (a : A) :
    AlgebraTrace.normalizedAlgebraTrace (A := B) (Units.map (algebraMap R S) u) (algebraMap A B a) =
      algebraMap R S (AlgebraTrace.normalizedAlgebraTrace (A := A) u a) := by
  have hp : Algebra.IsPushout R S A B := CommRingCat.isPushout_iff_isPushout.mp h
  exact Free.AlgebraTraceBaseChange.normalizedAlgebraTrace_baseChange b (IsScalarTower.toAlgHom R A B) hp.out u a

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.TracePushout
