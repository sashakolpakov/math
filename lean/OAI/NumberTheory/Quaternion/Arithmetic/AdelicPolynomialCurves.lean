import OAI.NumberTheory.Quaternion.Arithmetic.IntegralPolynomialCurves
import OAI.NumberTheory.Quaternion.Arithmetic.SelectedArithmeticProduct
import OAI.NumberTheory.Quaternion.Arithmetic.ScalarApproximation

/-! # Adelic Polynomial Curves -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AdelicPolynomialCurves

noncomputable section

section

/-! Additive strong approximation places every independently supported
value of a ground-field polynomial additive curve in the adelic closure
of the rational group. -/

open scoped Classical _root_.NumberField RestrictedProduct
open IsDedekindDomain Filter Set

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

omit [NumberField F] in
theorem awayFinitePlace_injective (S : Finset (LocalAdeles.Place F))
    (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S) :
    Function.Injective (SelectedArithmeticProduct.awayFinitePlace S harch) := by
  intro v w h
  apply Subtype.ext
  rw [← SelectedArithmeticProduct.inr_awayFinitePlace S harch v, ← SelectedArithmeticProduct.inr_awayFinitePlace S harch w]
  exact congrArg Sum.inr h

theorem localPointsPlaceEquiv_mem_integral (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    {v w : LocalAdeles.Place F} (h : v = w) (g : LocalAdeles.LocalPoints G v) :
    SelectedArithmeticProduct.localPointsPlaceEquiv G h g ∈ LocalAdeles.integralLocalSubgroup G w ↔ g ∈ LocalAdeles.integralLocalSubgroup G v := by
  subst w
  rfl

variable (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
  (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S)
  (u : PolynomialAdditiveCurves.PolynomialAdditiveCurve G)

def finiteCurveToAwayPoint (v : ApproximationTopology.AwayPlace S) (t : (SelectedArithmeticProduct.awayFinitePlace S harch v).adicCompletion F) :
    LocalAdeles.LocalPoints G v.val :=
  SelectedArithmeticProduct.localPointsPlaceEquiv G (SelectedArithmeticProduct.inr_awayFinitePlace S harch v)
    (u.hom _ (LocalAdeles.localEmbedding (.inr (SelectedArithmeticProduct.awayFinitePlace S harch v))) (Multiplicative.ofAdd t))

theorem finiteCurveToAwayPoint_continuous (v : ApproximationTopology.AwayPlace S) :
    Continuous (finiteCurveToAwayPoint G S harch u v) :=
  (SelectedArithmeticProduct.localPointsPlaceEquiv G (SelectedArithmeticProduct.inr_awayFinitePlace S harch v)).continuous.comp
    (u.continuous_point (LocalAdeles.localEmbedding (.inr (SelectedArithmeticProduct.awayFinitePlace S harch v))))

theorem finiteCurveToAwayPoint_zero (v : ApproximationTopology.AwayPlace S) :
    finiteCurveToAwayPoint G S harch u v 0 = 1 := by
  change SelectedArithmeticProduct.localPointsPlaceEquiv G _ (u.hom _ _ 1) = 1
  rw [map_one, map_one]

theorem finiteCurveToAwayPoint_rational (v : ApproximationTopology.AwayPlace S) (t : F) :
    finiteCurveToAwayPoint G S harch u v
      (algebraMap F ((SelectedArithmeticProduct.awayFinitePlace S harch v).adicCompletion F) t) =
      LocalAdeles.diagonalLocal G v.val (u.hom F (RingHom.id F) (Multiplicative.ofAdd t)) := by
  unfold finiteCurveToAwayPoint
  have he := u.map_point (RingHom.id F)
    (LocalAdeles.localEmbedding (.inr (SelectedArithmeticProduct.awayFinitePlace S harch v))) t
  have hd : u.hom _ (LocalAdeles.localEmbedding (.inr (SelectedArithmeticProduct.awayFinitePlace S harch v)))
      (Multiplicative.ofAdd (algebraMap F ((SelectedArithmeticProduct.awayFinitePlace S harch v).adicCompletion F) t)) =
      LocalAdeles.diagonalLocal G (.inr (SelectedArithmeticProduct.awayFinitePlace S harch v))
        (u.hom F (RingHom.id F) (Multiplicative.ofAdd t)) := by
    simpa only [RingHom.comp_id] using! he.symm
  rw [hd]
  exact SelectedArithmeticProduct.localPointsPlaceEquiv_diagonal G _ _

theorem finiteCurveToAwayPoint_eventually_integral :
    ∀ᶠ v : ApproximationTopology.AwayPlace S in cofinite, MapsTo (finiteCurveToAwayPoint G S harch u v)
      ((SelectedArithmeticProduct.awayFinitePlace S harch v).adicCompletionIntegers F)
      (LocalAdeles.integralLocalSubgroup G v.val) := by
  have he := (Subtype.val_injective (p := fun v : LocalAdeles.Place F => v ∉ S)).tendsto_cofinite
    (IntegralPolynomialCurves.polynomialAdditiveCurve_eventually_integral G u)
  filter_upwards [he] with v hv
  intro t ht
  unfold finiteCurveToAwayPoint
  apply (localPointsPlaceEquiv_mem_integral G (SelectedArithmeticProduct.inr_awayFinitePlace S harch v) _).mpr
  have hv' : MapsTo
      (fun t : LocalAdeles.Completion (.inr (SelectedArithmeticProduct.awayFinitePlace S harch v)) =>
        u.hom _ (LocalAdeles.localEmbedding (.inr (SelectedArithmeticProduct.awayFinitePlace S harch v))) (Multiplicative.ofAdd t))
      (LocalAdeles.localIntegerRing (.inr (SelectedArithmeticProduct.awayFinitePlace S harch v)))
      (LocalAdeles.integralLocalSubgroup G (.inr (SelectedArithmeticProduct.awayFinitePlace S harch v))) := by
    rw [SelectedArithmeticProduct.inr_awayFinitePlace S harch v]
    exact hv
  exact hv' ht

def polynomialCurveAdelicMap : ScalarApproximation.ScalarFiniteAdeles F → LocalAdeles.AwayAdelicPoints G S :=
  RestrictedProduct.mapAlong (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v : ApproximationTopology.AwayPlace S => LocalAdeles.LocalPoints G v.val)
    (SelectedArithmeticProduct.awayFinitePlace S harch) (awayFinitePlace_injective S harch).tendsto_cofinite
    (finiteCurveToAwayPoint G S harch u) (finiteCurveToAwayPoint_eventually_integral G S harch u)

theorem polynomialCurveAdelicMap_continuous : Continuous (polynomialCurveAdelicMap G S harch u) :=
  RestrictedProduct.mapAlong_continuous _ _ _ _ _ _ (finiteCurveToAwayPoint_continuous G S harch u)

theorem polynomialCurveAdelicMap_rational (t : F) :
    polynomialCurveAdelicMap G S harch u (algebraMap F (ScalarApproximation.ScalarFiniteAdeles F) t) =
      LocalAdeles.diagonalAway G S (u.hom F (RingHom.id F) (Multiplicative.ofAdd t)) := by
  apply RestrictedProduct.ext
  intro v
  exact finiteCurveToAwayPoint_rational G S harch u v t

theorem polynomialCurveAdelicMap_mem_diagonal_closure (a : ScalarApproximation.ScalarFiniteAdeles F) :
    polynomialCurveAdelicMap G S harch u a ∈ (LocalAdeles.diagonalAway G S).range.topologicalClosure := by
  apply (ScalarApproximation.denseRange_scalarFiniteAdeles F).induction_on
    (p := fun a => polynomialCurveAdelicMap G S harch u a ∈
      (LocalAdeles.diagonalAway G S).range.topologicalClosure) a
    ((LocalAdeles.diagonalAway G S).range.isClosed_topologicalClosure.preimage
      (polynomialCurveAdelicMap_continuous G S harch u))
  intro t
  rw [polynomialCurveAdelicMap_rational]
  exact (LocalAdeles.diagonalAway G S).range.le_topologicalClosure (Set.mem_range_self _)

end

/-! A polynomial additive curve can be supported at one chosen local
factor inside the closure of the rational adelic diagonal. -/

open scoped Classical _root_.NumberField RestrictedProduct
open IsDedekindDomain Set

variable {F : Type} [Field F] [NumberField F] {n : ℕ}
  (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
  (harch : ∀ w : NumberField.InfinitePlace F, Sum.inl w ∈ S)
  (u : PolynomialAdditiveCurves.PolynomialAdditiveCurve G)

theorem polynomialCurveAdelicMap_single (v : ApproximationTopology.AwayPlace S)
    (t : (SelectedArithmeticProduct.awayFinitePlace S harch v).adicCompletion F) :
    polynomialCurveAdelicMap G S harch u
      (RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F)
        (SelectedArithmeticProduct.awayFinitePlace S harch v) t) =
      RestrictedProduct.mulSingle (fun w : ApproximationTopology.AwayPlace S => LocalAdeles.integralLocalSubgroup G w.val)
        v (finiteCurveToAwayPoint G S harch u v t) := by
  apply RestrictedProduct.ext
  intro w
  by_cases hw : w = v
  · subst w
    simp only [polynomialCurveAdelicMap, RestrictedProduct.mapAlong_apply,
      RestrictedProduct.single_eq_same, RestrictedProduct.mulSingle_eq_same]
  · have hf : SelectedArithmeticProduct.awayFinitePlace S harch w ≠ SelectedArithmeticProduct.awayFinitePlace S harch v :=
      fun h => hw (awayFinitePlace_injective S harch h)
    simp only [polynomialCurveAdelicMap, RestrictedProduct.mapAlong_apply,
      RestrictedProduct.single_eq_of_ne _ t hf, finiteCurveToAwayPoint_zero,
      RestrictedProduct.mulSingle_eq_of_ne _ _ hw]

theorem finiteCurveToAwayPoint_range (v : ApproximationTopology.AwayPlace S) :
    Set.range (finiteCurveToAwayPoint G S harch u v) =
      Set.range (fun t : LocalAdeles.Completion v.val => u.hom _ (LocalAdeles.localEmbedding v.val) (Multiplicative.ofAdd t)) := by
  obtain ⟨v, hv⟩ := v
  cases v with
  | inl w => exact (hv (harch w)).elim
  | inr w => rfl

include harch in
theorem supported_polynomial_curve_mem_diagonal_closure (v : ApproximationTopology.AwayPlace S) (t : LocalAdeles.Completion v.val) :
    RestrictedProduct.mulSingle (fun w : ApproximationTopology.AwayPlace S => LocalAdeles.integralLocalSubgroup G w.val) v
      (u.hom _ (LocalAdeles.localEmbedding v.val) (Multiplicative.ofAdd t)) ∈
        (LocalAdeles.diagonalAway G S).range.topologicalClosure := by
  have hr : u.hom _ (LocalAdeles.localEmbedding v.val) (Multiplicative.ofAdd t) ∈
      Set.range (finiteCurveToAwayPoint G S harch u v) := by
    rw [finiteCurveToAwayPoint_range]
    exact Set.mem_range_self t
  obtain ⟨s, hs⟩ := hr
  rw [← hs, ← polynomialCurveAdelicMap_single]
  exact polynomialCurveAdelicMap_mem_diagonal_closure G S harch u _

include harch in
theorem supported_rational_unipotent_mem_diagonal_closure
    (g : G.RationalPoints) (hg : IsNilpotent (PolynomialGaloisNorm.matrixPointsHom G (RingHom.id F) g - 1))
    (v : ApproximationTopology.AwayPlace S) :
    RestrictedProduct.mulSingle (fun w : ApproximationTopology.AwayPlace S => LocalAdeles.integralLocalSubgroup G w.val) v
      (LocalAdeles.diagonalLocal G v.val g) ∈ (LocalAdeles.diagonalAway G S).range.topologicalClosure := by
  obtain ⟨c, hc⟩ := PolynomialAdditiveCurves.unipotent_point_has_polynomialAdditiveCurve G g hg
  have he := c.map_point (RingHom.id F) (LocalAdeles.localEmbedding v.val) 1
  have hv : c.hom _ (LocalAdeles.localEmbedding v.val) (Multiplicative.ofAdd 1) = LocalAdeles.diagonalLocal G v.val g := by
    simpa only [hc, RingHom.comp_id, map_one] using! he.symm
  rw [← hv]
  exact supported_polynomial_curve_mem_diagonal_closure G S harch c v 1

end

end OAI.NumberTheory.Quaternion.Arithmetic.AdelicPolynomialCurves
