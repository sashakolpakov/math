import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulTensorTerms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KoszulEulerSums
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EulerShifts

/-! # Mixed Koszul Euler Difference -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulEulerDifference

noncomputable section

/-! The alternating Euler characteristic of the actual mixed Koszul
complex is a product of tensor-difference operators, one for each
section's line bundle. This retains the separate degrees of the cuts. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def mixedKoszulEuler {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (M : X.Modules) (bs : List (LineBundleKoszulComplex.LineBundleSection X)) : ℤ :=
  ∑ n ∈ Finset.range (bs.length + 1), (-1 : ℤ) ^ n *
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p ((LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs).X (-(n : ℤ)))

theorem mixedKoszulEuler_nil {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (M : X.Modules) :
    mixedKoszulEuler p M [] = CohomologyEulerCharacteristic.coefficientEulerCharacteristic p M := by
  simp [mixedKoszulEuler, LineBundleKoszulComplex.mixedLineBundleKoszulComplex]

theorem mixedKoszulEuler_coefficient_iso {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) {M N : X.Modules} (e : M ≅ N)
    (bs : List (LineBundleKoszulComplex.LineBundleSection X)) : mixedKoszulEuler p M bs = mixedKoszulEuler p N bs := by
  apply Finset.sum_congr rfl
  intro n _
  exact congrArg (fun z : ℤ => (-1 : ℤ) ^ n * z)
    (Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso p (MixedKoszulTensorTerms.mixedKoszul_coefficientTermIso e bs _))

theorem mixedKoszulEuler_tensor_terms {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X) (M : X.Modules) (bs : List (LineBundleKoszulComplex.LineBundleSection X)) :
    (∑ n ∈ Finset.range (bs.length + 1), (-1 : ℤ) ^ n * CohomologyEulerCharacteristic.coefficientEulerCharacteristic p
      ((LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor.obj
        ((LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs).X (-(n : ℤ))))) =
      mixedKoszulEuler p ((LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor.obj M) bs := by
  apply Finset.sum_congr rfl
  intro n _
  exact congrArg (fun z : ℤ => (-1 : ℤ) ^ n * z)
    (Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso p (MixedKoszulTensorTerms.mixedKoszul_tensorTermIso L M bs _))

theorem mixedKoszulEuler_cons {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [IsProper p] (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (b : LineBundleKoszulComplex.LineBundleSection X) (bs : List (LineBundleKoszulComplex.LineBundleSection X)) :
    mixedKoszulEuler p M (b :: bs) =
      mixedKoszulEuler p ((LineBundle.TensorEquivalence.lineBundleTensorEquivalence b.1).functor.obj M) bs -
        mixedKoszulEuler p M bs := by
  let C := LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs
  let F := (LineBundle.TensorEquivalence.lineBundleTensorEquivalence b.1).functor
  have hq (i : ℤ) : (C.X i).IsQuasicoherent := (LineBundleKoszulComplex.mixedLineBundleKoszulComplex_coherent M bs i).1
  have ht (i : ℤ) : (C.X i).IsFiniteType := (LineBundleKoszulComplex.mixedLineBundleKoszulComplex_coherent M bs i).2
  have hfq (i : ℤ) : (F.obj (C.X i)).IsQuasicoherent := LeftTensorCoherence.lineBundleTensorLeft_quasicoherent b.1 _
  have hft (i : ℤ) : (F.obj (C.X i)).IsFiniteType := LeftTensorCoherence.lineBundleTensorLeft_finiteType b.1 _
  have he (i : ℤ) : CohomologyEulerCharacteristic.coefficientEulerCharacteristic p ((LineBundle.SectionKoszulStep.lineBundleSectionKoszulStep b.1 b.2 C).X i) =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (C.X (i + 1)) + CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (F.obj (C.X i)) :=
    (Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso p
      (LineBundle.KoszulTermIsomorphisms.lineBundleSectionKoszulStep_XIsoBiprod b.1 b.2 C i)).trans (Proper.CoherentEulerBiprod.proper_coherent_euler_biprod p _ _)
  let a : ℕ → ℤ := fun n => CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (C.X (-(n : ℤ)))
  let e : ℕ → ℤ := fun n => CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (F.obj (C.X (-(n : ℤ))))
  let c : ℕ → ℤ := fun n =>
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p ((LineBundle.SectionKoszulStep.lineBundleSectionKoszulStep b.1 b.2 C).X (-(n : ℤ)))
  have hz : c 0 = e 0 := by
    have h1 : CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (C.X 1) = 0 :=
      Bounded.ExactEuler.coefficientEulerCharacteristic_of_isZero p _
        (LineBundleKoszulComplex.mixedLineBundleKoszulComplex_isZero_X M bs 1 (Or.inr (by omega)))
    change CohomologyEulerCharacteristic.coefficientEulerCharacteristic p ((LineBundle.SectionKoszulStep.lineBundleSectionKoszulStep b.1 b.2 C).X 0) =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (F.obj (C.X 0))
    simpa only [zero_add, h1] using he 0
  have hs (n : ℕ) : c (n + 1) = a n + e (n + 1) := by
    have hi : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by omega
    change CohomologyEulerCharacteristic.coefficientEulerCharacteristic p ((LineBundle.SectionKoszulStep.lineBundleSectionKoszulStep b.1 b.2 C).X (-((n + 1 : ℕ) : ℤ))) =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (C.X (-(n : ℤ))) +
        CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (F.obj (C.X (-((n + 1 : ℕ) : ℤ))))
    rw [he, hi]
  have hlast : IsZero (C.X (-((bs.length + 1 : ℕ) : ℤ))) :=
    LineBundleKoszulComplex.mixedLineBundleKoszulComplex_isZero_X M bs _ (Or.inl (by omega))
  have haz : a (bs.length + 1) = 0 := Bounded.ExactEuler.coefficientEulerCharacteristic_of_isZero p _ hlast
  have hez : e (bs.length + 1) = 0 := Bounded.ExactEuler.coefficientEulerCharacteristic_of_isZero p _ (Functor.map_isZero F hlast)
  have h := AlternatingConeSums.alternating_cone_sum a e c hz hs bs.length haz hez
  calc
    mixedKoszulEuler p M (b :: bs) =
        (∑ n ∈ Finset.range (bs.length + 1), (-1 : ℤ) ^ n * CohomologyEulerCharacteristic.coefficientEulerCharacteristic p
          (F.obj (C.X (-(n : ℤ))))) - mixedKoszulEuler p M bs := h
    _ = _ := congrArg (fun z => z - mixedKoszulEuler p M bs)
      (mixedKoszulEuler_tensor_terms p b.1 M bs)

def mixedLineBundleEulerDifference (X : Scheme.{u}) :
    List (LineBundleKoszulComplex.LineBundleSection X) → AddMonoid.End (Line.Bundles.LineBundle.IsoClass X → ℤ)
  | [] => 1
  | b :: bs => (LineBundle.EulerShifts.lineBundleEulerShift X (Line.Bundles.LineBundle.classOf b.1) - 1) * mixedLineBundleEulerDifference X bs

theorem mixedKoszulEuler_eq_difference {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [IsProper p] (M : Line.Bundles.LineBundle X) (bs : List (LineBundleKoszulComplex.LineBundleSection X)) :
    mixedKoszulEuler p M.sheaf bs =
      MixedKoszulEulerDifference.mixedLineBundleEulerDifference X bs (LineBundle.EulerShifts.lineBundleClassEuler p) (Line.Bundles.LineBundle.classOf M) := by
  induction bs generalizing M with
  | nil =>
    rw [mixedKoszulEuler_nil]
    rfl
  | cons b bs ih =>
    have : M.sheaf.IsQuasicoherent := M.isQuasicoherent
    have : M.sheaf.IsFiniteType := M.isFiniteType
    let e : (LineBundle.TensorEquivalence.lineBundleTensorEquivalence b.1).functor.obj M.sheaf ≅ (M.tensor b.1).sheaf :=
      LineBundle.TensorEquivalence.lineBundleTensorEquivalence_objIso b.1 M.sheaf ≪≫ Tensor.ProductSheaf.tensorModuleCommIso b.1.sheaf M.sheaf
    rw [mixedKoszulEuler_cons p M.sheaf b bs, mixedKoszulEuler_coefficient_iso p e bs,
      ih (M.tensor b.1), ih M]
    change _ = MixedKoszulEulerDifference.mixedLineBundleEulerDifference X bs (LineBundle.EulerShifts.lineBundleClassEuler p)
      (Line.Bundles.LineBundle.classOf M * Line.Bundles.LineBundle.classOf b.1) -
      MixedKoszulEulerDifference.mixedLineBundleEulerDifference X bs (LineBundle.EulerShifts.lineBundleClassEuler p) (Line.Bundles.LineBundle.classOf M)
    rw [Line.Bundles.LineBundle.classOf_tensor]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulEulerDifference
