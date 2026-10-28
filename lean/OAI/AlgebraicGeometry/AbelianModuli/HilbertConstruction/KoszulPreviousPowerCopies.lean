import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.RetractCopies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KoszulTopTensorPower
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.KoszulTermIsomorphisms

/-! # Koszul Previous Power Copies -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KoszulPreviousPowerCopies

noncomputable section

/-! The term before the last Koszul term is a finite retract of copies
of the power exactly two degrees below the last power. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}}

theorem lineBundleSquareKoszul_previousTerm_finiteRetractCopies (G : Line.Bundles.LineBundle X)
    (ss : List (Line.Bundles.structureModule X ⟶ (G.tensorPower 2).sheaf)) (b : ℕ) :
    Finite.RetractCopies.FiniteRetractCopies (G.tensorPower ((ss.length - 1) * 2 + b)).sheaf
      ((LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex (G.tensorPower 2) (G.tensorPower b).sheaf ss).X (-1)) := by
  induction ss with
  | nil =>
    exact Finite.RetractCopies.FiniteRetractCopies.of_isZero _ _
      (LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex_isZero_X (G.tensorPower 2) (G.tensorPower b).sheaf [] (-1)
        (Or.inl (by simp)))
  | cons s ss ih =>
    let L := G.tensorPower 2
    let C := LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex L (G.tensorPower b).sheaf ss
    let F := (LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor
    have : F.Additive := Functor.additive_of_preserves_binary_products F
    let Q := (G.tensorPower (ss.length * 2 + b)).sheaf
    have hzero : Finite.RetractCopies.FiniteRetractCopies Q (C.X 0) :=
      (Finite.RetractCopies.FiniteRetractCopies.self Q).of_targetIso (KoszulTopTensorPower.lineBundleSquareKoszulTopPowerIso G ss b).symm
    have htail : Finite.RetractCopies.FiniteRetractCopies Q (F.obj (C.X (-1))) := by
      by_cases hnil : ss = []
      · subst ss
        exact Finite.RetractCopies.FiniteRetractCopies.of_isZero Q _ (F.map_isZero
          (LineBundle.SectionKoszulComplex.lineBundleSectionKoszulComplex_isZero_X L (G.tensorPower b).sheaf [] (-1)
            (Or.inl (by simp))))
      · have hlen : 0 < ss.length := by
          by_contra hn
          exact hnil (List.length_eq_zero_iff.mp (by omega))
        let q := (ss.length - 1) * 2 + b
        have hq : 2 + q = ss.length * 2 + b := by dsimp [q]; omega
        let e : F.obj (G.tensorPower q).sheaf ≅ Q :=
          LineBundle.TensorEquivalence.lineBundleTensorEquivalence_objIso L (G.tensorPower q).sheaf ≪≫
            (G.tensorPowerAddIso 2 q).symm ≪≫
              eqToIso (congrArg (fun n => (G.tensorPower n).sheaf) hq)
        exact (ih.map F).of_sourceIso e
    change Finite.RetractCopies.FiniteRetractCopies Q ((LineBundle.SectionKoszulStep.lineBundleSectionKoszulStep L s C).X (-1))
    apply (hzero.biprod htail).of_targetIso
    simpa only [F, show (-1 : ℤ) + 1 = 0 by decide] using
      (LineBundle.KoszulTermIsomorphisms.lineBundleSectionKoszulStep_XIsoBiprod L s C (-1)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KoszulPreviousPowerCopies
