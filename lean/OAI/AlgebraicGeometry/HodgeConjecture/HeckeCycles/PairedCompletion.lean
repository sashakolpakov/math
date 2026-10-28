import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Completion
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource

/-! # Paired Completion -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PairedCompletion.CM

noncomputable section

/-! Reindex the integral local decomposition by the source's actual
conjugate pairs, in the convention used by TateComparison. -/

open scoped Classical TensorProduct
open TensorProduct _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Completion.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E]
  [IsGalois ℚ E] [NumberField.IsCMField E]
  {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
  {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
  (places : GeometricSource.CM.Places E)

def placeIndex (p : Fin places.count × Bool) : Gal(E/ℚ) :=
  if p.2 then ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative p.1 else places.representative p.1

def pairedCharacter (p : Fin places.count × Bool) : RingOfIntegers E →+* ℤ_[q] :=
  j.localCharacter iota (placeIndex E places p)

/-- This is the same integral tensor map used in TateComparison's good-prime
predicate, with the characters supplied by CMPoints. -/
def pairedCompletion :
    ℤ_[q] ⊗[ℤ] RingOfIntegers E →ₐ[ℤ] (Fin places.count × Bool → ℤ_[q]) :=
  Algebra.TensorProduct.lift
    (algebraMap ℤ_[q] (Fin places.count × Bool → ℤ_[q])).toIntAlgHom
    (RingHom.pi (pairedCharacter E j iota places)).toIntAlgHom
    (fun _ _ => Commute.all _ _)

omit [IsGalois ℚ E] in
theorem pairedCompletion_apply (x : ℤ_[q] ⊗[ℤ] RingOfIntegers E)
    (p : Fin places.count × Bool) :
    pairedCompletion E j iota places x p =
      Local.Completion.CM.completionLinear j iota x (placeIndex E places p) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem pairedCompletion_bijective (hsplit : j.HasSplitCoordinates iota) :
    Function.Bijective (pairedCompletion E j iota places) := by
  let e := Equiv.ofBijective (placeIndex E places) places.complete
  have h := Local.Completion.CM.completion_bijective j iota hsplit
  constructor
  · intro x y hxy
    apply h.1
    funext τ
    obtain ⟨p, rfl⟩ := places.complete.2 τ
    simpa only [pairedCompletion_apply, placeIndex] using congrFun hxy p
  · intro y
    obtain ⟨x, hx⟩ := h.2 (fun τ => y (e.symm τ))
    refine ⟨x, ?_⟩
    funext p
    rw [pairedCompletion_apply, hx]
    exact congrArg y (e.symm_apply_apply p)

theorem localCharacter_conjugate (τ : Gal(E/ℚ)) (a : RingOfIntegers E) :
    j.localCharacter iota (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) a =
      j.localCharacter iota τ (IsCMField.ringOfIntegersComplexConj E a) := by
  apply congrArg j.integralEmbedding
  apply Subtype.ext
  change iota ((ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) (a : E)) = iota (τ (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (a : E)))
  exact congrArg iota (congrArg (fun σ : Gal(E/ℚ) => σ (a : E))
    (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_commute E τ).eq)

/-- Exchanging the pair label composes the integral character with the
actual CM involution on the ring of integers. -/
theorem pairedCharacter_conjugate (v : Fin places.count) (side : Bool)
    (a : RingOfIntegers E) :
    pairedCharacter E j iota places (v, !side) a =
      pairedCharacter E j iota places (v, side)
        (IsCMField.ringOfIntegersComplexConj E a) := by
  cases side
  · exact localCharacter_conjugate E j iota _ a
  · have h := localCharacter_conjugate E j iota (places.representative v)
      (IsCMField.ringOfIntegersComplexConj E a)
    have haa : IsCMField.ringOfIntegersComplexConj E
        (IsCMField.ringOfIntegersComplexConj E a) = a := by
      apply Subtype.ext
      exact IsCMField.complexConj_apply_apply E a
    rw [haa] at h
    exact h.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PairedCompletion.CM
