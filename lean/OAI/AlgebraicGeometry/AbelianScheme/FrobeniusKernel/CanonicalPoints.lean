import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Canonical
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalOppositePoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalBlockComponents
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ProductFactorization

/-! # Canonical Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalPoints.Construction

noncomputable section

/-! The constructed full native kernel realizes exactly the independent
all-test prescription used in the full FrobeniusKernel statement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (hgood : q.Coprime (∏ i, δ i))
variable (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (hc : ∀ v, labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
variable (P : ∀ v : Fin s, CartierModel.Construction.CartierCoordinates (.of k)
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))
variable (H : ∀ v : Fin s, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))

def prescribedKernelComponentCondition (T : Over (Spec (.of k)))
    (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) (v : Fin s) : Prop :=
  (∃ h : T ⟶ (H v).group.X,
    Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (H v) T h =
      Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (v, false)) T x) ∧
  ∀ (U : Over (Spec (.of k))) (t : U ⟶ T) (h : U ⟶ (H v).group.X),
    Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) U
      (Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (H v) U h)
      (Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n (labels (v, true)) U
        ((A.abelian.torsionFunctor (q ^ n)).map t.op x))

abbrev canonicalFullKernelBlockMap :=
  BlockProducts.Construction.groupBlockProductMap s (fun v => (P v).pairedKernel (H v).coordinates (H v).inclusion)
    (CMPointsSplitting.Construction.l45PairedBlockFamily j iota hsplit A.abelian ρ n s labels)
    (fun v => (H v).inclusion ⊗ₘ (P v).oppositeInclusion (H v).coordinates (H v).inclusion
      (CanonicalIntrinsicPairing.Construction.canonicalPairingAtLevel j iota hsplit A ρ hρ hgood
        (labels (v, false)) (labels (v, true)) (hc v) n (P v)))

theorem canonicalFullKernel_point (T : Over (Spec (.of k)))
    (z : T ⟶ (CMPointsKernels.Construction.l45FullChosenKernel j iota hsplit A ρ n s labels P H).X) :
    z ≫ Canonical.Construction.canonicalFullKernelInclusion j iota hsplit A ρ hρ hgood n s labels hc P H =
      (CMPointsSplitting.Construction.l45FullBlockPointsEquiv j iota hsplit A.abelian ρ n s labels T
        (z ≫ (canonicalFullKernelBlockMap j iota hsplit A ρ hρ hgood n s labels hc P H).hom.hom)).val := by
  let f := (canonicalFullKernelBlockMap j iota hsplit A ρ hρ hgood n s labels hc P H).hom.hom
  let b := (CMPointsSplitting.Construction.l45FullTorsionSplitting j iota hsplit A.abelian ρ n s labels).inv.hom.hom
  change z ≫ ((f ≫ b) ≫ A.abelian.torsionInclusion (q ^ n)) = _
  exact (Category.assoc z (f ≫ b) (A.abelian.torsionInclusion (q ^ n))).symm.trans
    ((congrArg (fun t => t ≫ A.abelian.torsionInclusion (q ^ n)) (Category.assoc z f b).symm).trans
      (CMPointsSplittingPoints.Construction.l45FullTorsionSplitting_inv_inclusion j iota hsplit A.abelian ρ n s labels T (z ≫ f)))

theorem canonicalPairedBlockFactor_iff (T : Over (Spec (.of k)))
    (b : T ⟶ (BlockProducts.Construction.groupBlockProduct s (CMPointsSplitting.Construction.l45PairedBlockFamily j iota hsplit A.abelian ρ n s labels)).X)
    (v : Fin s) :
    (∃ z : T ⟶ ((P v).pairedKernel (H v).coordinates (H v).inclusion).X,
      z ≫ ((H v).inclusion ⊗ₘ (P v).oppositeInclusion (H v).coordinates (H v).inclusion
        (CanonicalIntrinsicPairing.Construction.canonicalPairingAtLevel j iota hsplit A ρ hρ hgood
          (labels (v, false)) (labels (v, true)) (hc v) n (P v))).hom.hom =
      ProductPoints.Construction.groupBlockProductPointsEquiv s (CMPointsSplitting.Construction.l45PairedBlockFamily j iota hsplit A.abelian ρ n s labels) T b v) ↔
    prescribedKernelComponentCondition j iota hsplit A ρ n s labels H T
      (CMPointsSplitting.Construction.l45FullBlockPointsEquiv j iota hsplit A.abelian ρ n s labels T b) v := by
  let z := ProductPoints.Construction.groupBlockProductPointsEquiv s (CMPointsSplitting.Construction.l45PairedBlockFamily j iota hsplit A.abelian ρ n s labels) T b v
  refine (ProductFactorization.Construction.groupPairMap_factor_iff (H v).inclusion
    ((P v).oppositeInclusion (H v).coordinates (H v).inclusion
      (CanonicalIntrinsicPairing.Construction.canonicalPairingAtLevel j iota hsplit A ρ hρ hgood
        (labels (v, false)) (labels (v, true)) (hc v) n (P v))) T z).trans (and_congr ?_ ?_)
  · have hl := CanonicalBlockComponents.Construction.canonicalFullBlockComponent_false j iota hsplit A ρ n s labels T b v
    constructor
    · rintro ⟨h, hh⟩
      exact ⟨h, (congrArg (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n (labels (v, false)) T) hh).trans hl⟩
    · rintro ⟨h, hh⟩
      exact ⟨h, CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint_injective j iota hsplit A ρ n (labels (v, false)) T
        (hh.trans hl.symm)⟩
  · refine (CanonicalOppositePoints.Construction.canonicalOppositeKernel_realizes j iota hsplit A ρ hρ hgood
      (labels (v, false)) (labels (v, true)) (hc v) n (P v) (H v) T (z ≫ snd _ _)).trans ?_
    apply forall_congr'
    intro U
    apply forall_congr'
    intro t
    apply forall_congr'
    intro h
    have hr := CanonicalBlockComponents.Construction.canonicalFullBlockComponent_true j iota hsplit A ρ n s labels T b v
    have hn := CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint_natural j iota hsplit A ρ n (labels (v, true)) t (z ≫ snd _ _)
    have hp := CanonicalBlockComponents.Construction.prescribedBlockComponent_natural j iota hsplit A ρ n (labels (v, true)) t
      (CMPointsSplitting.Construction.l45FullBlockPointsEquiv j iota hsplit A.abelian ρ n s labels T b)
    have he := hn.symm.trans ((congrArg ((A.abelian.torsionFunctor (q ^ n)).map t.op) hr).trans hp)
    exact iff_of_eq (congrArg (fun y => Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n)
      (pow_pos (Fact.out : q.Prime).pos n) U
      (Prescription.Construction.prescribedChosenPoint j iota hsplit A ρ n (labels (v, false)) (H v) U h) y) he)

theorem canonicalFullKernelBlockMap_realizes (T : Over (Spec (.of k)))
    (b : T ⟶ (BlockProducts.Construction.groupBlockProduct s (CMPointsSplitting.Construction.l45PairedBlockFamily j iota hsplit A.abelian ρ n s labels)).X) :
    (∃ z : T ⟶ (CMPointsKernels.Construction.l45FullChosenKernel j iota hsplit A ρ n s labels P H).X,
      z ≫ (canonicalFullKernelBlockMap j iota hsplit A ρ hρ hgood n s labels hc P H).hom.hom = b) ↔
      ∀ v, prescribedKernelComponentCondition j iota hsplit A ρ n s labels H T
        (CMPointsSplitting.Construction.l45FullBlockPointsEquiv j iota hsplit A.abelian ρ n s labels T b) v :=
  (ProductFactorization.Construction.groupBlockProductMap_factor_iff s _ _ _ T b).trans
    (forall_congr' (fun v => canonicalPairedBlockFactor_iff j iota hsplit A ρ hρ hgood n s labels hc P H T b v))

theorem canonicalFullKernel_realizes (T : Over (Spec (.of k))) (a : T ⟶ A.abelian.scheme) :
    (∃ z : T ⟶ (CMPointsKernels.Construction.l45FullChosenKernel j iota hsplit A ρ n s labels P H).X,
      z ≫ Canonical.Construction.canonicalFullKernelInclusion j iota hsplit A ρ hρ hgood n s labels hc P H = a) ↔
      Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H T a := by
  constructor
  · rintro ⟨z, hz⟩
    let b := z ≫ (canonicalFullKernelBlockMap j iota hsplit A ρ hρ hgood n s labels hc P H).hom.hom
    refine ⟨CMPointsSplitting.Construction.l45FullBlockPointsEquiv j iota hsplit A.abelian ρ n s labels T b,
      (canonicalFullKernel_point j iota hsplit A ρ hρ hgood n s labels hc P H T z).symm.trans hz, ?_⟩
    exact (canonicalFullKernelBlockMap_realizes j iota hsplit A ρ hρ hgood n s labels hc P H T b).mp ⟨z, rfl⟩
  · rintro ⟨x, hx, hcond⟩
    let e := CMPointsSplitting.Construction.l45FullBlockPointsEquiv j iota hsplit A.abelian ρ n s labels T
    let b := e.symm x
    have hb : e b = x := e.apply_symm_apply x
    obtain ⟨z, hz⟩ := (canonicalFullKernelBlockMap_realizes j iota hsplit A ρ hρ hgood n s labels hc P H T b).mpr
      (show ∀ v, prescribedKernelComponentCondition j iota hsplit A ρ n s labels H T (e b) v from
        hb.symm ▸ hcond)
    refine ⟨z, (canonicalFullKernel_point j iota hsplit A ρ hρ hgood n s labels hc P H T z).trans ?_⟩
    exact (congrArg (fun t => (e t).val) hz).trans ((congrArg Subtype.val hb).trans hx)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalPoints.Construction
