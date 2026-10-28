import OAI.AlgebraicGeometry.PELModuli.CMPoints.Models
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexBlockCard
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.FiberProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter

/-! # Component Height Bound -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! The actual arithmetic sections supplied by IntegralModel give one complex
fiber per integral component. A single bound controls the block counts
in all of these finitely many native fibers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : Models.RankThreePELModel E K)

def Models.RankThreePELModel.integralComponentInclusion (a : M.Family) (t : Fin (M.componentCount a)) :
    (M.components a).S t ⟶ (M.integral a).toOver :=
  Sigma.ι (M.components a).S t ≫ (M.decomposition a).hom

def Models.RankThreePELModel.componentPolarized (a : M.Family) (t : Fin (M.componentCount a)) :=
  (M.integral a).universal.data.polarized.pullback (M.integralComponentInclusion a t).left

abbrev Models.RankThreePELModel.componentAbelian (a : M.Family) (t : Fin (M.componentCount a)) :=
  (M.componentPolarized a t).abelian

def Models.RankThreePELModel.componentAction (a : M.Family) (t : Fin (M.componentCount a)) :
    AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (M.componentAbelian a t) :=
  (M.integral a).universal.data.action.pullback (M.integralComponentInclusion a t).left

def Models.RankThreePELModel.componentComplexSection (a : M.Family) (t : Fin (M.componentCount a)) :
    Foundations.Scheme.ProjectiveSpace.complexBase ⟶ ((M.components a).S t).left :=
  M.arithmetic.complexPoint ≫ ((M.components a).x₀ t).left

abbrev Models.RankThreePELModel.componentComplexAbelian (a : M.Family) (t : Fin (M.componentCount a)) :=
  (M.componentAbelian a t).pullback (M.componentComplexSection a t)

def Models.RankThreePELModel.componentComplexAction (a : M.Family) (t : Fin (M.componentCount a)) :
    AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (M.componentComplexAbelian a t) :=
  (M.componentAction a t).pullback (M.componentComplexSection a t)

def Models.RankThreePELModel.componentComplexPresentation (a : M.Family) (t : Fin (M.componentCount a)) :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation (M.componentComplexAbelian a t).scheme.left
      (M.componentComplexAbelian a t).scheme.hom :=
  AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation
    ((M.componentPolarized a t).geometricFiber_projectivePresentation ℂ (M.componentComplexSection a t))

theorem Models.RankThreePELModel.exists_component_complex_block_bound (hM : M.HasPrescribedBallPeriods) :
    ∃ D : ℕ, ∀ (q : ℕ) (hq : q.Prime),
      letI : Fact q.Prime := ⟨hq⟩
      ∀ j : M.QadicChoice q, j.HasSplitCoordinates M.extendedEmbedding → D < q →
        ∀ (a : M.Family) (t : Fin (M.componentCount a)) (n : ℕ) (τ : Gal(E/ℚ)),
          Nat.card (BlocksProjectors.blockPoints (M.componentComplexAbelian a t) (M.componentComplexAction a t)
            (j.localCharacter M.extendedEmbedding τ) n
            (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) = q ^ (3 * n) := by
  classical
  let I := Σ a : M.Family, Fin (M.componentCount a)
  have hex (z : I) := ComplexBlockCard.exists_complex_block_bound (κ := M.arithmetic.embedding) M.extendedEmbedding
    (M.componentComplexAbelian z.1 z.2) (M.componentComplexPresentation z.1 z.2)
    (M.componentComplexAction z.1 z.2) M.s hM.1 rfl hM.2.1
  choose d _ hd using hex
  refine ⟨∑ z : I, d z, fun q hq => ?_⟩
  let : Fact q.Prime := ⟨hq⟩
  intro j hsplit hb a t n τ
  have hz : d ⟨a, t⟩ ≤ ∑ z : I, d z :=
    Finset.single_le_sum (fun z _ => Nat.zero_le (d z)) (Finset.mem_univ (⟨a, t⟩ : I))
  exact hd ⟨a, t⟩ q hq j hsplit (lt_of_le_of_lt hz hb) n τ

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
