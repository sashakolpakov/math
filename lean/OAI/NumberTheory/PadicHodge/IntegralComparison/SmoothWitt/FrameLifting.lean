import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCover
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SmoothNil

/-! # Frame Lifting -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameLifting

noncomputable section

/-! A smooth Witt lift maps to the ambient ring of every actual crystalline thickening. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k A C : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Algebra.Smooth (WittVector p k) A]
  [CommRing C] [Algebra k C] (ρ : A →+* C)
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w))
  (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))

local notation "W" => WittVector p k

@[instance_reducible]
def ambientAlgebra : Algebra W U.ring := U.base.toAlgebra

def closedMap : letI := ambientAlgebra p k C U
    A →ₐ[W] U.ring ⧸ U.ideal := by
  letI := ambientAlgebra p k C U
  refine { (BigCrystallineCover.closedRingMap p k C U).comp ρ with commutes' := ?_ }
  intro w
  change BigCrystallineCover.closedRingMap p k C U (ρ (algebraMap W A w)) =
    Ideal.Quotient.mk U.ideal (U.base w)
  rw [hbase]
  exact RingHom.congr_fun (BigCrystallineCover.closedRingMap_coefficients p k C U) w

omit [Fintype k] in
include hbase in
theorem exists_lift : ∃ l : A →+* U.ring,
    (Ideal.Quotient.mk U.ideal).comp l = (BigCrystallineCover.closedRingMap p k C U).comp ρ ∧
      l.comp (algebraMap W A) = U.base := by
  let := ambientAlgebra p k C U
  obtain ⟨l, hl⟩ := AlgebraicGeometry.Crystalline.Cohomology.SmoothNil.SmoothNilLifting.exists_lift (closedMap p k A C ρ hbase U)
    (Ideal.Quotient.mkₐ W U.ideal) Ideal.Quotient.mk_surjective
      (fun b hb => U.nilIdeal b (Ideal.Quotient.eq_zero_iff_mem.mp hb))
  exact ⟨l.toRingHom, congrArg AlgHom.toRingHom hl, l.comp_algebraMap⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameLifting
