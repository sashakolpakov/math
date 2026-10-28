import OAI.AlgebraicGeometry.Comparison.Betti.EmptySupportZeroCycles
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.CechVanishing

/-! # Zero Cycles -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.ZeroCycles.Dolbeault

noncomputable section

section

/-! Original projective twist zero cycles are determined by their empty Laurent support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] SectorProperSupportContraction.Dolbeault.properSupportCoefficients_addCommGroup SectorProperSupportContraction.Dolbeault.properSupportCochains_addCommGroup SectorProperSupportContraction.Dolbeault.supportCochains_addZeroClass

abbrev projectiveTwistZeroCycles (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :=
  (((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj
    (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).d 0 1).hom.ker

theorem projectiveTwistZeroCycle_support_cycle (n : ℕ) (j : Fin (n + 1)) (d : ℤ)
    (z : projectiveTwistZeroCycles n j d) (J : Finset (Fin (n + 1))) :
    SupportedCochains.Cech.supportedCechDifferential J 0 (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d 0 z.val J) = 0 := by
  have hd := Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates_differential n j d 0 z.val J
  have hz : ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj
    (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).d 0 1 z.val = 0 := z.property
  have he := congrArg (fun a : ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj
      (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X 1 =>
    Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d 1 a J) hz
  exact hd.symm.trans (he.trans (congrFun (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d 1).map_zero J))

def projectiveTwistZeroCycleCoefficient (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :
    projectiveTwistZeroCycles n j d →+
      ↥(HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (∅ : Finset (Fin (n + 1))) d) where
  toFun z := (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d 0 z.val ∅).val (fun _ => 0)
  map_zero' := congrArg (fun s : Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d 0
    (∅ : Finset (Fin (n + 1))) => s.val (fun _ => 0))
      (congrFun (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d 0).map_zero ∅)
  map_add' z w := congrArg (fun s : Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d 0
    (∅ : Finset (Fin (n + 1))) => s.val (fun _ => 0))
      (congrFun ((Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d 0).map_add z.val w.val) ∅)

theorem projectiveTwistZeroCycleCoefficient_injective (n : ℕ) (j : Fin (n + 2)) (d : ℤ) :
    Function.Injective (projectiveTwistZeroCycleCoefficient (n + 1) j d) := by
  intro z w h
  apply Subtype.ext
  apply (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates (n + 1) j d 0).injective
  funext J
  have hz := projectiveTwistZeroCycle_support_cycle (n + 1) j d z J
  have hw := projectiveTwistZeroCycle_support_cycle (n + 1) j d w J
  by_cases hJ : J = ∅
  · subst J
    apply Subtype.ext
    funext t
    exact (EmptySupportZeroCycles.Cech.supportedZeroCycle_eq_constant ∅ _ hz (0 : Fin (n + 2)) t).trans
      (h.trans (EmptySupportZeroCycles.Cech.supportedZeroCycle_eq_constant ∅ _ hw (0 : Fin (n + 2)) t).symm)
  · have hJN : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr hJ
    exact (SupportedZeroCycles.Cech.supportedZeroCycle_zero_of_nonempty J hJN _ hz).trans
      (SupportedZeroCycles.Cech.supportedZeroCycle_zero_of_nonempty J hJN _ hw).symm

end

/-! Every empty-support homogeneous coefficient gives an original projective zero cocycle. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] SectorProperSupportContraction.Dolbeault.properSupportCoefficients_addCommGroup SectorProperSupportContraction.Dolbeault.properSupportCochains_addCommGroup SectorProperSupportContraction.Dolbeault.supportCochains_addZeroClass

def projectiveTwistZeroRepresentative (n : ℕ) (j : Fin (n + 1)) (d : ℤ)
    (v : HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (∅ : Finset (Fin (n + 1))) d) :
    ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).X 0 :=
  (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d 0).symm (Pi.single ∅ (EmptySupportZeroCycles.Cech.emptySupportConstantCochain v))

theorem projectiveTwistZeroRepresentative_coordinates (n : ℕ) (j : Fin (n + 1)) (d : ℤ)
    (v : HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (∅ : Finset (Fin (n + 1))) d) :
    Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d 0 (projectiveTwistZeroRepresentative n j d v) =
      Pi.single ∅ (EmptySupportZeroCycles.Cech.emptySupportConstantCochain v) :=
  (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d 0).apply_symm_apply _

theorem projectiveTwistZeroRepresentative_cycle (n : ℕ) (j : Fin (n + 1)) (d : ℤ)
    (v : HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (∅ : Finset (Fin (n + 1))) d) :
    ((cechComplexFunctor (Projective.Intersections.Dolbeault.projectiveStandardCover n)).obj
      (AcyclicCover.Dolbeault.projectiveTwistAdditiveSheaf n j d).obj).d 0 1 (projectiveTwistZeroRepresentative n j d v) = 0 := by
  apply (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d 1).injective
  funext J
  have hd := Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates_differential n j d 0
    (projectiveTwistZeroRepresentative n j d v) J
  have hc := congrFun (projectiveTwistZeroRepresentative_coordinates n j d v) J
  let T : ∀ J : Finset (Fin (n + 1)), Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d 0 J :=
    Pi.single ∅ (EmptySupportZeroCycles.Cech.emptySupportConstantCochain v)
  have hzero : SupportedCochains.Cech.supportedCechDifferential J 0 (T J) = 0 := by
    by_cases hJ : J = ∅
    · subst J
      simpa only [T, Pi.single_eq_same] using EmptySupportZeroCycles.Cech.emptySupportConstantCochain_cycle (ι := Fin (n + 1)) v
    · simp only [T, Pi.single_eq_of_ne hJ, map_zero]
  exact hd.trans ((congrArg (SupportedCochains.Cech.supportedCechDifferential J 0) hc).trans
    (hzero.trans (congrFun (Projective.SectorSupportDifferential.Dolbeault.projectiveTwistCechSupportCoordinates n j d 1).map_zero J).symm))

theorem projectiveTwistZeroCycleCoefficient_surjective (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :
    Function.Surjective (projectiveTwistZeroCycleCoefficient n j d) := by
  intro v
  refine ⟨⟨projectiveTwistZeroRepresentative n j d v, projectiveTwistZeroRepresentative_cycle n j d v⟩, ?_⟩
  have h := congrFun (projectiveTwistZeroRepresentative_coordinates n j d v) ∅
  have he := congrArg (fun s : Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d 0
    (∅ : Finset (Fin (n + 1))) => s.val (fun _ => 0)) h
  exact he.trans (congrArg (fun s : Laurent.SectorCochainProduct.Dolbeault.homogeneousSectorSupportedCochains d 0
    (∅ : Finset (Fin (n + 1))) => s.val (fun _ => 0)) (Pi.single_eq_same _ _))

def projectiveTwistZeroCycleCoefficientEquiv (n : ℕ) (j : Fin (n + 2)) (d : ℤ) :
    projectiveTwistZeroCycles (n + 1) j d ≃+
      ↥(HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (∅ : Finset (Fin (n + 2))) d) :=
  AddEquiv.ofBijective (projectiveTwistZeroCycleCoefficient (n + 1) j d)
    ⟨projectiveTwistZeroCycleCoefficient_injective n j d,
      projectiveTwistZeroCycleCoefficient_surjective (n + 1) j d⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.ZeroCycles.Dolbeault
