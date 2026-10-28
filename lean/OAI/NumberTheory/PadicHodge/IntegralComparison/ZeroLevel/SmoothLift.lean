import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.WittBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCover
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SmoothNil

/-! # Smooth Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.SmoothLift

noncomputable section

/-!
# IntegralComparison: smooth residue-field charts lift into original zeroth-level crystalline objects
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u

variable (p : ℕ) [Fact p.Prime] (k C : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C]
  (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))
  (h : (p : U.ring) = 0)

@[instance_reducible]
def ambientAlgebra : Algebra k U.ring := (Bounded.WittBase.residueBase p k U h).toAlgebra

def closedAlgebraMap :
    letI := ambientAlgebra p k C U h
    C →ₐ[k] U.ring ⧸ U.ideal := by
  letI := ambientAlgebra p k C U h
  refine { BigCrystallineCover.closedRingMap p k C U with commutes' := ?_ }
  intro a
  obtain ⟨w, rfl⟩ := WittVector.constantCoeff_surjective p a
  change BigCrystallineCover.closedRingMap p k C U (algebraMap k C (WittVector.constantCoeff w)) =
    Ideal.Quotient.mk U.ideal (Bounded.WittBase.residueBase p k U h (WittVector.constantCoeff w))
  rw [show Bounded.WittBase.residueBase p k U h (WittVector.constantCoeff w) = U.base w from
    RingHom.congr_fun (Bounded.WittBase.residueBase_constantCoeff p k U h) w]
  exact RingHom.congr_fun (BigCrystallineCover.closedRingMap_coefficients p k C U) w

theorem exists_lift [Algebra.Smooth k C] :
    ∃ l : C →+* U.ring,
      (Ideal.Quotient.mk U.ideal).comp l = BigCrystallineCover.closedRingMap p k C U ∧
        l.comp (algebraMap k C) = Bounded.WittBase.residueBase p k U h := by
  let := ambientAlgebra p k C U h
  have hn : ∀ b ∈ RingHom.ker (Ideal.Quotient.mkₐ k U.ideal).toRingHom, IsNilpotent b := by
    intro b hb
    exact U.nilIdeal b (Ideal.Quotient.eq_zero_iff_mem.mp hb)
  obtain ⟨l, hl⟩ := AlgebraicGeometry.Crystalline.Cohomology.SmoothNil.SmoothNilLifting.exists_lift (closedAlgebraMap p k C U h)
    (Ideal.Quotient.mkₐ k U.ideal) Ideal.Quotient.mk_surjective hn
  exact ⟨l.toRingHom, congrArg AlgHom.toRingHom hl, l.comp_algebraMap⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.SmoothLift
