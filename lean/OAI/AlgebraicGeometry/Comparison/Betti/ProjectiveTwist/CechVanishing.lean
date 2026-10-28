import OAI.AlgebraicGeometry.Comparison.Betti.SupportCochainVanishing
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechSupportReduction
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # Cech Vanishing -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.CechVanishing.Dolbeault

/-! Original positive-degree projective twist cocycles are boundaries away from top degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] SectorProperSupportContraction.Dolbeault.properSupportCoefficients_addCommGroup SectorProperSupportContraction.Dolbeault.properSupportCochains_addCommGroup SectorProperSupportContraction.Dolbeault.supportCochains_addZeroClass

theorem projectiveTwistCechSupportCycle (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (z : ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X (q + 1))
    (hz : ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).d
      (q + 1) (q + 2) z = 0) (J : Finset (Fin (n + 1))) :
    SupportedCochains.Cech.supportedCechDifferential J (q + 1) (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d (q + 1) z J) = 0 := by
  have hd := Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates_differential n j d (q + 1) z J
  have he := congrArg (fun a : ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj
      (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X (q + 2) =>
    Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d (q + 2) a J) hz
  exact hd.symm.trans (he.trans (congrFun (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d (q + 2)).map_zero J))

theorem projectiveTwistCechCycle_boundary_of_ne_top (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (hq : q + 1 ≠ n)
    (z : ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X (q + 1))
    (hz : ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).d
      (q + 1) (q + 2) z = 0) :
    ∃ b : ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X q,
      ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).d
        q (q + 1) b = z := by
  have hcard : q + 2 ≠ Fintype.card (Fin (n + 1)) := by
    intro h
    have h' : q + 2 = n + 1 := by simpa only [Fintype.card_fin] using h
    exact hq (Nat.succ.inj h')
  let Z := Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d (q + 1) z
  have hex (J : Finset (Fin (n + 1))) :
      ∃ t : Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d q J, SupportedCochains.Cech.supportedCechDifferential J q t = Z J :=
    SupportCochainVanishing.Cech.supportedCechCycle_has_primitive_of_card_ne (V := ↥(HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients J d))
      J q hcard (Z J) (projectiveTwistCechSupportCycle n j d q z hz J)
  let T : ∀ J : Finset (Fin (n + 1)), Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d q J :=
    fun J => Classical.choose (hex J)
  have hT (J : Finset (Fin (n + 1))) : SupportedCochains.Cech.supportedCechDifferential J q (T J) = Z J :=
    Classical.choose_spec (hex J)
  refine ⟨(Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d q).symm T, ?_⟩
  apply (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d (q + 1)).injective
  funext J
  have hd := Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates_differential n j d q
    ((Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d q).symm T) J
  have hi := congrFun ((Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d q).apply_symm_apply T) J
  exact hd.trans ((congrArg (SupportedCochains.Cech.supportedCechDifferential J q) hi).trans (hT J))

end AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.CechVanishing.Dolbeault

namespace AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.CechVanishing

/-! Actual analytified projective twist cohomology vanishes in positive degrees
different from the dimension of projective space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

section

theorem additiveCochain_exactAt_of_boundaries (K : CochainComplex AddCommGrpCat ℕ) (q : ℕ)
    (h : ∀ z : K.X (q + 1), K.d (q + 1) (q + 2) z = 0 →
      ∃ b : K.X q, K.d q (q + 1) b = z) : K.ExactAt (q + 1) := by
  rw [K.exactAt_iff' q (q + 1) (q + 2) (by simp) (by simp)]
  exact (ShortComplex.ab_exact_iff _).2 h

end

namespace Dolbeault

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveTwistCech_exactAt_of_ne_top (n : ℕ) (j : Fin (n + 1)) (d : ℤ) (q : ℕ)
    (hq : q + 1 ≠ n) :
    ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj
      (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).ExactAt (q + 1) :=
  additiveCochain_exactAt_of_boundaries _ q
    (projectiveTwistCechCycle_boundary_of_ne_top n j d q hq)

theorem projectiveTwist_cohomology_vanish_of_ne_top (n : ℕ) (j : Fin (n + 1))
    (d : ℤ) (q : ℕ) (hq : q + 1 ≠ n) :
    Subsingleton (Sheaf.H.{0} (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d) (q + 1)) := by
  have h := (projectiveTwistCech_exactAt_of_ne_top n j d q hq).isZero_homology
  have hH := h.of_iso (AcyclicCover.Dolbeault.projectiveTwistCechComparison n j d q).symm
  exact AddCommGrpCat.isZero_iff_subsingleton.mp hH

end Dolbeault

end AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.CechVanishing

end

end OAI
