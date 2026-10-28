import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.KoszulTermIsomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionKoszulCoherent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.CoherentEulerBiprod
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlternatingConeSums
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.CochainEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.LineBundleEuler

/-! # Koszul Euler Sums -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KoszulEulerSums

noncomputable section

/-! The alternating Euler sum of the actual section Koszul complex satisfies the tensor finite-difference recurrence. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

local instance e33KoszulEulerSumTensorAdditive {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) :
    (LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

def lineBundleKoszulEuler {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (L : Line.Bundles.LineBundle X) (M : X.Modules)
    (ss : List (Line.Bundles.structureModule X ⟶ L.sheaf)) : ℤ :=
  ∑ n ∈ Finset.range (ss.length + 1), (-1 : ℤ) ^ n *
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p ((LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss).X (-(n : ℤ)))

theorem lineBundleKoszulEuler_nil {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (L : Line.Bundles.LineBundle X) (M : X.Modules) :
    lineBundleKoszulEuler p L M [] = CohomologyEulerCharacteristic.coefficientEulerCharacteristic p M := by
  simp [lineBundleKoszulEuler, LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex]

theorem lineBundleKoszulEuler_coefficient_iso {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (L : Line.Bundles.LineBundle X) {M N : X.Modules} (e : M ≅ N)
    (ss : List (Line.Bundles.structureModule X ⟶ L.sheaf)) :
    lineBundleKoszulEuler p L M ss = lineBundleKoszulEuler p L N ss := by
  apply Finset.sum_congr rfl
  intro n _
  exact congrArg (fun z : ℤ => (-1 : ℤ) ^ n * z)
    (Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso p (LineBundle.KoszulTermIsomorphisms.lineBundleKoszul_coefficientTermIso L e ss _))

theorem lineBundleKoszulEuler_tensor_terms {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (L : Line.Bundles.LineBundle X) (M : X.Modules)
    (ss : List (Line.Bundles.structureModule X ⟶ L.sheaf)) :
    (∑ n ∈ Finset.range (ss.length + 1), (-1 : ℤ) ^ n * CohomologyEulerCharacteristic.coefficientEulerCharacteristic p
      ((LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor.obj
        ((LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss).X (-(n : ℤ))))) =
      lineBundleKoszulEuler p L ((LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor.obj M) ss := by
  apply Finset.sum_congr rfl
  intro n _
  exact congrArg (fun z : ℤ => (-1 : ℤ) ^ n * z)
    (Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso p (LineBundle.KoszulTermIsomorphisms.lineBundleKoszul_tensorTermIso L M ss _))

theorem lineBundleKoszulEuler_cons {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] (L : Line.Bundles.LineBundle X) (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType]
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (ss : List (Line.Bundles.structureModule X ⟶ L.sheaf)) :
    lineBundleKoszulEuler p L M (s :: ss) =
      lineBundleKoszulEuler p L ((LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor.obj M) ss -
        lineBundleKoszulEuler p L M ss := by
  let C := LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss
  let F := (LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor
  have hq (i : ℤ) : (C.X i).IsQuasicoherent := (LineBundle.SectionKoszulCoherent.lineBundleSectionKoszulComplex_coherent L M ss i).1
  have ht (i : ℤ) : (C.X i).IsFiniteType := (LineBundle.SectionKoszulCoherent.lineBundleSectionKoszulComplex_coherent L M ss i).2
  have hfq (i : ℤ) : (F.obj (C.X i)).IsQuasicoherent := LeftTensorCoherence.lineBundleTensorLeft_quasicoherent L _
  have hft (i : ℤ) : (F.obj (C.X i)).IsFiniteType := LeftTensorCoherence.lineBundleTensorLeft_finiteType L _
  have he (i : ℤ) : CohomologyEulerCharacteristic.coefficientEulerCharacteristic p ((LineBundle.SectionKoszulStep.lineBundleSectionKoszulStep L s C).X i) =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (C.X (i + 1)) + CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (F.obj (C.X i)) :=
    (Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso p
      (LineBundle.KoszulTermIsomorphisms.lineBundleSectionKoszulStep_XIsoBiprod L s C i)).trans (Proper.CoherentEulerBiprod.proper_coherent_euler_biprod p _ _)
  let a : ℕ → ℤ := fun n => CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (C.X (-(n : ℤ)))
  let b : ℕ → ℤ := fun n => CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (F.obj (C.X (-(n : ℤ))))
  let c : ℕ → ℤ := fun n =>
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic p ((LineBundle.SectionKoszulStep.lineBundleSectionKoszulStep L s C).X (-(n : ℤ)))
  have hz : c 0 = b 0 := by
    have h1 : CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (C.X 1) = 0 :=
      Bounded.ExactEuler.coefficientEulerCharacteristic_of_isZero p _
        (LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex_isZero_X L M ss 1 (Or.inr (by omega)))
    change CohomologyEulerCharacteristic.coefficientEulerCharacteristic p ((LineBundle.SectionKoszulStep.lineBundleSectionKoszulStep L s C).X 0) =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (F.obj (C.X 0))
    simpa only [zero_add, h1] using he 0
  have hs (n : ℕ) : c (n + 1) = a n + b (n + 1) := by
    have hi : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by omega
    change CohomologyEulerCharacteristic.coefficientEulerCharacteristic p ((LineBundle.SectionKoszulStep.lineBundleSectionKoszulStep L s C).X (-((n + 1 : ℕ) : ℤ))) =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (C.X (-(n : ℤ))) +
        CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (F.obj (C.X (-((n + 1 : ℕ) : ℤ))))
    rw [he, hi]
  have hlast : IsZero (C.X (-((ss.length + 1 : ℕ) : ℤ))) :=
    LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex_isZero_X L M ss _ (Or.inl (by omega))
  have ha : a (ss.length + 1) = 0 := Bounded.ExactEuler.coefficientEulerCharacteristic_of_isZero p _ hlast
  have hb : b (ss.length + 1) = 0 :=
    Bounded.ExactEuler.coefficientEulerCharacteristic_of_isZero p _ (Functor.map_isZero F hlast)
  have h := AlternatingConeSums.alternating_cone_sum a b c hz hs ss.length ha hb
  calc
    lineBundleKoszulEuler p L M (s :: ss) =
        (∑ n ∈ Finset.range (ss.length + 1), (-1 : ℤ) ^ n * CohomologyEulerCharacteristic.coefficientEulerCharacteristic p
          (F.obj (C.X (-(n : ℤ))))) - lineBundleKoszulEuler p L M ss := h
    _ = _ := congrArg (fun z => z - lineBundleKoszulEuler p L M ss)
      (lineBundleKoszulEuler_tensor_terms p L M ss)

theorem lineBundleKoszulEuler_eq_zero_of_acyclic {k : Type u} [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (p : X ⟶ Spec (.of k)) [IsProper p] (L : Line.Bundles.LineBundle X) (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (ss : List (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hs : (LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss).Acyclic) : lineBundleKoszulEuler p L M ss = 0 := by
  have hq (i : ℤ) : ((LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss).X i).IsQuasicoherent :=
    (LineBundle.SectionKoszulCoherent.lineBundleSectionKoszulComplex_coherent L M ss i).1
  have ht (i : ℤ) : ((LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex L M ss).X i).IsFiniteType :=
    (LineBundle.SectionKoszulCoherent.lineBundleSectionKoszulComplex_coherent L M ss i).2
  exact Coherent.CochainEuler.proper_coherent_acyclic_euler_sum p _ hs ss.length
    (LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex_isZero_X L M ss 1 (Or.inr (by omega)))
    (LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex_isZero_X L M ss (-(ss.length : ℤ) - 1) (Or.inl (by omega)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KoszulEulerSums
