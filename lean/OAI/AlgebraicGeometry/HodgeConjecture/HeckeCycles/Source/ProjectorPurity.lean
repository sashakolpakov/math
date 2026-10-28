import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Comparison
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.ComparisonEmbeddingPurity
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Identity
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonAction

/-! # Projector Purity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ProjectorPurity.CM

noncomputable section

/-! Apply original ordinary comparison to the actual source Hecke
projector. Its coefficient transport, nonzero range, and Hodge structure
are identified with those required by the proved purity theorem. -/

open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Comap.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BettiComparison.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ProjectorTransport.CM

theorem map_ne_bot {F U V : Type*} [Field F]
    [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
    (e : U ≃ₗ[F] V) (S : Submodule F U) (hS : S ≠ ⊥) : S.map e.toLinearMap ≠ ⊥ := by
  intro hz
  exact hS (Submodule.map_injective_of_injective e.injective
    (hz.trans (Submodule.map_bot e.toLinearMap).symm))

theorem same_action_range {F U I : Type*} [Field F]
    [AddCommGroup U] [Module ℚ U] [Algebra ℚ F]
    (T S : I → Module.End ℚ U) (h : ∀ i, T i = S i)
    (P : Module.End F (F ⊗[ℚ] U)) (χ : I → F)
    (hP : LinearMap.range P = HeckeCharacters.CM.Projectors.jointSpace (fun i => (S i).baseChange F) χ) :
    LinearMap.range P = HeckeCharacters.CM.Projectors.jointSpace (fun i => (T i).baseChange F) χ := by
  exact hP.trans (congrArg (fun A : I → Module.End ℚ U =>
    HeckeCharacters.CM.Projectors.jointSpace (fun i => (A i).baseChange F) χ) (funext h).symm)

theorem sign_bounds_transfer {U : Type*} [AddCommGroup U] [Module ℚ U]
    (H K : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (hh : H.holomorphic = K.holomorphic)
    (ha : H.antiholomorphic = K.antiholomorphic)
    (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification U)) (sign : Bool)
    (hb : let slope : ℚ := 1 / 2 - (ComplexMultiplication.SignSwitch.CM.signValue sign : ℚ) * (-3 / 2) / 3
      (slope = 0 ∨ slope = 1) ∧
        (slope = 1 ↔ LinearMap.range P ≤ K.holomorphic) ∧
        (slope = 0 ↔ LinearMap.range P ≤ K.antiholomorphic)) :
    (sign = true ↔ LinearMap.range P ≤ H.holomorphic) ∧
    (sign = false ↔ LinearMap.range P ≤ H.antiholomorphic) := by
  have hr := hb.2
  rw [← hh, ← ha] at hr
  cases sign <;> norm_num [ComplexMultiplication.SignSwitch.CM.signValue] at hr ⊢ <;> exact hr

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q)
  (hcop : Nat.Coprime q D.pel.denominator) (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])

local notation "AM" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseModel.CM.comparisonModel D.pel hg j hcop

variable (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel) (fullSide : Fin s → Bool)

local notation "idx" => fun i => A.basis
  (Subtype.val (Neighbor.Types.CM.integralType D.pel.reference.distinguished fullSide i))

theorem bounds :
    letI : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke s q) := TateComparisonAction.CM.commutativeHeckeRing s q hElementaryDivisors
    ∀ (R : (AM).HeckeRealization (AbelianScheme.TateComparison.HeckeKernel.Hecke s q))
    (_hbetti : (AM).bettiHecke D.pel.complexEmbedding R = (fun h => A.cohomologyAction h))
    (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput)
    (_hc : Constructed.Comparison.CM.Conclusion AM j.fieldInClosure j.complexClosure j.iota R idx)
    (χ : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar)
    (_hχ : HeckeCharacters.CM.Projectors.jointSpace (fun h => (A.cohomologyAction h).baseChange ℂ)
      (fun h => j.complexClosure (χ h)) ≠ ⊥)
    (τ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ)) (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification D.pel.H1))
    (_hP : P ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace (CMExtraction.Intrinsic.Base.nativeH1 D hHodgeDecomposition hg) (CMExtraction.Intrinsic.Base.nativeH1 D hHodgeDecomposition hg))
    (_hRange : LinearMap.range P = HeckeCharacters.CM.Projectors.jointSpace (fun h => (A.cohomologyAction h).baseChange ℂ)
      (fun h => j.complexClosure (τ (χ h))))
    (_hne : LinearMap.range P ≠ ⊥)
    (b z : CMExtraction.ParameterChoices.Qbar) (_hnorm : ‖j.complexClosure z‖ = 1)
    (_hcentral : ∃ n : ℕ, 0 < n ∧ (b ^ 3 * z) ^ n = 1)
    (_hvalues : ∀ i : Fin 3, τ (χ (idx i)) =
      (![(q : CMExtraction.ParameterChoices.Qbar) * b * (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure + (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure)⁻¹ + z),
        (q : CMExtraction.ParameterChoices.Qbar) * b ^ 2 * (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure * (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure)⁻¹ +
          CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure * z + (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure)⁻¹ * z),
        b ^ 3 * z] : Fin 3 → CMExtraction.ParameterChoices.Qbar) i)
    (sign : Bool) (_hsign : NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q j.iota z = (ComplexMultiplication.SignSwitch.CM.signValue sign : ℚ) * (-3 / 2)),
    (sign = true ↔ LinearMap.range P ≤ (CMExtraction.Intrinsic.Base.nativeH1 D hHodgeDecomposition hg).holomorphic) ∧
    (sign = false ↔ LinearMap.range P ≤ (CMExtraction.Intrinsic.Base.nativeH1 D hHodgeDecomposition hg).antiholomorphic)  := by
  let : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke s q) := TateComparisonAction.CM.commutativeHeckeRing s q hElementaryDivisors
  intro R hbetti hHodgeDecomposition hc χ hχ τ P hP hRange hne b z hnorm hcentral hvalues sign hsign
  let : FiniteDimensional ℚ ((AM).Betti D.pel.complexEmbedding) :=
    (Constructed.Comap.CM.hodge AM D.pel.complexEmbedding).finiteDimensional
  have hχC : (AM).bettiHeckeSummand D.pel.complexEmbedding R
      (fun h => j.complexClosure (χ h)) ≠ ⊥ := by
    have hm := BettiComparison.CM.Summands.betti_summand_identification AM D.pel.complexEmbedding R
      (fun h => j.complexClosure (χ h))
    rw [hbetti] at hm
    rw [← hm]
    exact map_ne_bot (BettiComparison.CM.coefficientEquiv AM D.pel.complexEmbedding) _ hχ
  have hpH : P ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace (Constructed.Comap.CM.hodge AM D.pel.complexEmbedding)
      (Constructed.Comap.CM.hodge AM D.pel.complexEmbedding) :=
    (congrArg (fun S => P ∈ S) (Comparison.CM.hom_subspace D hg j hcop hHodgeDecomposition)).mp hP
  let P' : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification ((AM).Betti D.pel.complexEmbedding)) := P
  have hpR : LinearMap.range (Intrinsic.ProjectorTransport.CM.projector AM D.pel.complexEmbedding P') =
      (AM).bettiHeckeSummand D.pel.complexEmbedding R
        (fun h => j.complexClosure (τ (χ h))) :=
    Intrinsic.ProjectorTransport.CM.range_of_character AM D.pel.complexEmbedding R P' _
      (same_action_range (fun h => Constructed.Comap.CM.heckeAction AM D.pel.complexEmbedding R h)
        (fun h => A.cohomologyAction h)
        (fun h => (Constructed.Comap.CM.heckeAction_apply AM D.pel.complexEmbedding R h).trans (congrFun hbetti h))
        P' _ hRange)
  have hpN : LinearMap.range (Intrinsic.ProjectorTransport.CM.projector AM D.pel.complexEmbedding P') ≠ ⊥ :=
    (congrArg (fun S => S ≠ ⊥)
      (Intrinsic.ProjectorTransport.CM.projector_range AM D.pel.complexEmbedding P')).mpr
        (map_ne_bot (BettiComparison.CM.coefficientEquiv AM D.pel.complexEmbedding) _ hne)
  have hp := Constructed.ComparisonEmbeddingPurity.CM.bounds AM j.fieldInClosure j.complexClosure j.iota R idx
    D.pel.complexEmbedding j.complex_compatibility hc χ hχC τ P' hpH hpR hpN
    (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure) b z (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt_sq q j.complexClosure)
    (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt_image q j.complexClosure) hnorm hcentral hvalues sign (-3 / 2) (Or.inl rfl) hsign
  exact sign_bounds_transfer (CMExtraction.Intrinsic.Base.nativeH1 D hHodgeDecomposition hg) (Constructed.Comap.CM.hodge AM D.pel.complexEmbedding)
    (Comparison.CM.holomorphic D hg j hcop hHodgeDecomposition)
    (Comparison.CM.antiholomorphic D hg j hcop hHodgeDecomposition) P sign hp

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ProjectorPurity.CM
