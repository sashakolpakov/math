import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SupportPlaces
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlaceAt

/-! # Truncated Lower -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TruncatedLower.CM.Quadratic

/-! Truncating quadratic coefficients to sufficiently many primes
preserves the action on any fixed finite Schwartz function exactly. -/

open scoped Classical _root_.Matrix
open Filter
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlaceAt.CM.Mask
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Quadratic.CM
variable {I : Type*} [Fintype I]

theorem tail_quadratic_integral (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (hB : ∀ i j v, v ∉ S → (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * B i j) v ∈ v.adicCompletionIntegers ℚ)
    (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hx : ∀ i v, v ∉ S → x i v ∈ v.adicCompletionIntegers ℚ) :
    RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic (PlaceAt.CM.Mask.matrixMask Sᶜ B) x ∈ RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele := by
  rw [RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization.ringQuadratic_entries]
  apply RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.sum_mem
  intro i _
  apply RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.integralAdele.sum_mem
  intro j _ v
  change SymplecticLocal.CM.localEval v
    (x i * (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * PlaceAt.CM.Mask.matrixMask Sᶜ B i j) * x j) ∈ v.adicCompletionIntegers ℚ
  simp only [map_mul]
  change x i v * ((algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2)) v * PlaceAt.CM.Mask.mask Sᶜ (B i j) v) * x j v ∈ v.adicCompletionIntegers ℚ
  rw [PlaceAt.CM.Mask.mask_eval]
  simp only [Set.mem_compl_iff]
  by_cases hv : v ∈ S
  · rw [ite_eq_right (not_not.mpr hv), mul_zero, mul_zero, zero_mul]
    exact (v.adicCompletionIntegers ℚ).zero_mem
  · rw [ite_eq_left hv]
    exact (v.adicCompletionIntegers ℚ).mul_mem _ _
      ((v.adicCompletionIntegers ℚ).mul_mem _ _ (hx i v hv) (hB i j v hv)) (hx j v hv)

theorem tail_fixes (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (hB : ∀ i j v, v ∉ S → (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * B i j) v ∈ v.adicCompletionIntegers ℚ)
    (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I)
    (hf : ∀ x ∈ tsupport f.val, ∀ i v, v ∉ S → x i v ∈ v.adicCompletionIntegers ℚ) :
    Quadratic.CM.finiteQuadratic (PlaceAt.CM.Mask.matrixMask Sᶜ B) f = f := by
  apply Subtype.ext
  funext x
  rw [Quadratic.CM.finiteQuadratic_apply]
  by_cases hx : f.val x = 0
  · rw [hx, mul_zero]
  · rw [Constructed.AdelicCharacter.CM.Finite.character_integral _
      (tail_quadratic_integral S B hB x (hf x (subset_tsupport f.val hx))), one_mul]

theorem exists_truncation (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    ∃ S : Finset RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, ∀ T : Finset RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, S ⊆ T →
      Quadratic.CM.finiteQuadratic (PlaceAt.CM.Mask.matrixMask (T : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) B) f = Quadratic.CM.finiteQuadratic B f := by
  have hB : ∀ᶠ v in cofinite, ∀ i j,
      (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * B i j) v ∈ v.adicCompletionIntegers ℚ := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    exact (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * B i j).property
  have he := hB.and (SupportPlaces.CM.compact_eventually_integral
    (tsupport f.val) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_hasCompactSupport f))
  have hbad : {v | ¬((∀ i j, (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * B i j) v ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ x ∈ tsupport f.val, ∀ i, x i v ∈ v.adicCompletionIntegers ℚ))}.Finite := he
  refine ⟨hbad.toFinset, ?_⟩
  intro T hT
  have hg (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hv : v ∉ T) :
      (∀ i j, (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (1 / 2) * B i j) v ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ x ∈ tsupport f.val, ∀ i, x i v ∈ v.adicCompletionIntegers ℚ) := by
    have hs : v ∉ hbad.toFinset := fun h => hv (hT h)
    simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hs
  have ht := tail_fixes (T : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) B
    (fun i j v hv => (hg v hv).1 i j) f (fun x hx i v hv => (hg v hv).2 x hx i)
  have hh := congrArg (fun U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I => U f)
    (PlaceAt.CM.QuadraticAddition.operator_add (PlaceAt.CM.Mask.matrixMask (T : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) B)
      (PlaceAt.CM.Mask.matrixMask (T : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace)ᶜ B))
  rw [PlaceAt.CM.Mask.matrixMask_add_compl] at hh
  change Quadratic.CM.finiteQuadratic B f = Quadratic.CM.finiteQuadratic (PlaceAt.CM.Mask.matrixMask (T : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) B)
    (Quadratic.CM.finiteQuadratic (PlaceAt.CM.Mask.matrixMask (T : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace)ᶜ B) f) at hh
  rw [ht] at hh
  exact hh.symm

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TruncatedLower.CM.Quadratic

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TruncatedLower.CM

/-! Exact finite-prime truncation for lower operators, obtained from
the proved quadratic truncation by the actual Fourier conjugation. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlaceAt.CM.Mask
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.IntegralVacuum.CM.LowerBare
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierHeisenberg.CM.Equiv

theorem mask_neg (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : PlaceAt.CM.Mask.mask S (-a) = -PlaceAt.CM.Mask.mask S a := by
  apply DFunLike.ext
  intro v
  change SymplecticLocal.CM.localEval v (PlaceAt.CM.Mask.mask S (-a)) =
    SymplecticLocal.CM.localEval v (-PlaceAt.CM.Mask.mask S a)
  rw [map_neg]
  change PlaceAt.CM.Mask.mask S (-a) v = -PlaceAt.CM.Mask.mask S a v
  rw [PlaceAt.CM.Mask.mask_eval, PlaceAt.CM.Mask.mask_eval]
  by_cases hv : v ∈ S
  · rw [ite_eq_left hv, ite_eq_left hv]
    exact (SymplecticLocal.CM.localEval v).map_neg a
  · rw [ite_eq_right hv, ite_eq_right hv, neg_zero]

variable {I : Type*} [Fintype I]

omit [Fintype I] in
theorem matrixMask_neg (S : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    PlaceAt.CM.Mask.matrixMask S (-B) = -PlaceAt.CM.Mask.matrixMask S B := by
  apply Matrix.ext
  intro i j
  exact mask_neg S (B i j)

theorem exists_truncation (B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hB : B.IsSymm) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    ∃ S : Finset RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, ∀ T : Finset RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, S ⊆ T →
      BareNe.CM.Group.bareAction
        (IntegralVacuum.CM.LowerBare.lowerLift (PlaceAt.CM.Mask.matrixMask (T : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) B) (PlaceAt.CM.Mask.matrixMask_symmetric _ B hB)) f =
      BareNe.CM.Group.bareAction (IntegralVacuum.CM.LowerBare.lowerLift B hB) f := by
  obtain ⟨S, hS⟩ := Quadratic.exists_truncation (-B) (FourierHeisenberg.CM.Equiv.fourierEquiv f)
  refine ⟨S, ?_⟩
  intro T hT
  change FourierHeisenberg.CM.Equiv.fourierEquiv.symm (Quadratic.CM.finiteQuadratic (-PlaceAt.CM.Mask.matrixMask (T : Set RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) B)
      (FourierHeisenberg.CM.Equiv.fourierEquiv f)) = FourierHeisenberg.CM.Equiv.fourierEquiv.symm (Quadratic.CM.finiteQuadratic (-B) (FourierHeisenberg.CM.Equiv.fourierEquiv f))
  apply congrArg FourierHeisenberg.CM.Equiv.fourierEquiv.symm
  rw [← matrixMask_neg]
  exact hS T hT

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TruncatedLower.CM

end

end OAI
