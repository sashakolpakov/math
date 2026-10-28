import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectiveOrdinaryReference
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.VanishingReferenceTheta
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GivenActionComparison
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceActiveIndex
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LabeledGoodPrime
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.Intrinsic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectiveGeometricThetaPrepared
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaRealization
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ConcreteRestriction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CofinalExtraction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ElementaryDivisors
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Definitions

/-! # Projective -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Projective.CM

noncomputable section

/-! HeckeCycles for the original source family, conditional on the complete named
prerequisites other than AdelicTheta. Projective openness, integral SL3
perfectness and the actual reference cover supply the original source
stabilization. The ordinary model, actual IsogenyQuotient correspondences, source
GeometricTheta witness, Hecke parameters, Hodge projectors, and cofinal restrictions
are constructed in the proof. -/

open scoped Classical TensorProduct _root_.NumberField BigOperators _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

theorem extraction_from_named_inputs
    (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)) (hv : v.val 1 = true)
    (d : Gal(E/ℚ) → Bool) (hd : ∀ τ, d τ = v.val τ⁻¹)
    (Nbase : ℕ) (hNbase : 0 < Nbase)
    (X : ℕ → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ∀ N, ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure ((X N).rationalCohomology 1))
    (hH : ∀ N, Albanese.Definitions.CM.HodgeComparison.IsCanonicalH1 (X N) (H N))
    (Θ : ∀ N, ComplexMultiplication.WeightOne.CM.Complexification ((X N).rationalCohomology 1))
    (hsource : GeometricSource.CM.IsSourceBallThetaFamily E d Nbase X Θ)
    (hCongruenceLevel : ∀ s, ReferenceDatum.CM.CongruenceLevelInput E s) (hReferenceFamily : Moduli.CM.ReferenceFamilyInput) (hIntegralModel : ArithmeticModels.CM.IntegralModelInput)
    (hNeighborCounting : Neighbor.Counting.CM.NeighborCountingInput)
    (hFrobeniusKernel : Isogenies.NeighborCounting.Prerequisites.FullFrobeniusKernelInput)
    (hCMPoints : AbelianScheme.FrobeniusKernel.CMPoints.Construction.CMPointsInput.{0, 0})
    (hCartierDuality : AbelianScheme.FrobeniusKernel.CartierDuality.Construction.FullCartierDualityInput.{0}) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput.{0})
    (hLefschetzNormalization : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LefschetzNormalization.Proposition E)
    (hCotangentBundle : ∀ (B A : Type) [CommSemiring B] [CommGroup A], @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.CotangentBundle.Proposition B A _ _)
    (hCompletedTheta : ∀ (I : Type) [Fintype I] [DecidableEq I], @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.Theta.Proposition I _ _)
    (hNormOneApproximation : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.NormOneApproximation.Proposition) (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0, 0, 0, 0})
    (hTateComparison : TateComparison.CM.TateComparisonInput) (hGeometricTheta : Geometric.Theta.CM.GeometricThetaInput)
    (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput) (hHodgeComparison : PELModuli.IntegralModel.AlbaneseCohomology.HodgeComparisonInput)
    (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput)
    (hElementaryDivisors : AbelianScheme.IsogenyQuotient.ElementaryDivisors.Construction.ElementaryDivisorsInput.{0})
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparisonAdapter.CM.ExtremeSlopes.GeometricComparisonInput)
    (hCMExtraction : MatchedLevelExtraction.CM.Construction.CMExtractionInput.{0, 0, 0, 0}) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ Nbase ∣ N₀ ∧
      ∀ N, 0 < N → N₀ ∣ N → Θ N ∈ MatchedLevelExtraction.CM.Construction.lineImageSpan E v (H N) := by
  obtain ⟨B, places, L, φ, P, hP, hb, hμ, hzero, N, hN3, _hbaseN, _hdeep, haux,
    F, hF, hball, _hintegral, hprepared, Yref, _component, hΛ, _hYref, ρ, formY, θY,
    hρ, hformY, hθY, N₀, hN₀, hbase, hrestrictions⟩ :=
    ProjectiveOrdinaryReference.CM.OrdinaryReference.source_family_has_prepared_zero_reference
      E d Nbase hNbase X H Θ hsource hCongruenceLevel hReferenceFamily hIntegralModel hNeighborCounting hFrobeniusKernel hCMPoints hCartierDuality hTorsionQuotient
      (fun _ : Fin 0 => ℚ) ∅ 0
  by_cases hzeroθ : θY = 0
  · refine ⟨N₀, hN₀, hbase, ?_⟩
    intro n hn hdiv
    obtain ⟨_π, f, _hπ, _hf, _hs, _hcomp, hθ⟩ := hrestrictions n hn hdiv
    rw [← hθ, hzeroθ, map_zero]
    exact Submodule.zero_mem _
  let : FiniteDimensional ℚ (Yref.rationalCohomology 1) :=
    (CMExtraction.Mem.canonicalH1 hHodgeDecomposition Yref.presentation).finiteDimensional
  have hnonzero := VanishingReferenceTheta.CM.nonzero_class_detected E L φ P hΛ
    Yref N ρ hρ formY hformY θY hθY hzeroθ
  obtain ⟨bound, _hboundpos, hprime, Bext, V, r, components, e, hM, hgeometry,
    bound', hbound', _hframes, hordinary⟩ := hprepared
  let M := Ordinary.Models.CM.singletonModel P (RingHom.id E) E.val.toRingHom N
    F Bext V r components e
  obtain ⟨q, hq, hordinary⟩ := hordinary
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨hlarge, _hexcluded, _hE, _hK, _hExt, _hfields, j, hsplit, Red,
    hgeomRed, labels, hlabels, hactive, hgood, hreductions⟩ := hordinary
  have hlarge' : bound < q := lt_of_le_of_lt ((le_max_right 0 bound).trans hbound') hlarge
  have hN : 0 < N := lt_of_lt_of_le (by decide : 0 < 3) hN3
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  obtain ⟨_, _, _, _, _, _, hsmooth, _⟩ := hM.2.2 (0 : Fin 1)
  let : Smooth V.toOver.hom := hsmooth
  have hpol : Nat.Coprime q (∏ i, P.polarizationType i) :=
    (Nat.coprime_pow_right_iff (by decide : 0 < 2) _ _).mp (Red.polarizationPrimeToQ (0 : Fin 1))
  obtain ⟨Cfine, hIsogenyQuotient⟩ := IsogenyQuotient.Intrinsic.CM.exists_paired_realization F hF E.val.toRingHom hball
    j M.extendedEmbedding hsplit (ReferenceDatum.CM.source_degree E places).1 (ReferenceDatum.CM.source_degree E places).2
    (Red.levelPrimeToQ (0 : Fin 1)) hpol V components e labels hlabels
  let C := IsogenyQuotient.Data.CM.correspondences F V Cfine
  let HD := Witt.PELSource.CM.heckeData (q := q) M (0 : Fin 1) C
    (fun (w : Fin places.count × Bool) => j.localCharacter M.extendedEmbedding (labels w))
  have hg : HD.HasIntegralModelGeometry := hgeometry q C (fun w => j.localCharacter M.extendedEmbedding (labels w))
  have hqD : HD.IsGoodCompletelySplitPrime := hgood (0 : Fin 1) C
  have hc46 : HD.RealizesIsogenyQuotient := hIsogenyQuotient
  let : Submodule.IsLattice ℚ P.lattice := ⟨hΛ.1, hΛ.2.1⟩
  let : Submodule.IsLattice ℚ HD.reference.lattice :=
    inferInstanceAs (Submodule.IsLattice ℚ P.lattice)
  let basis := Module.Free.chooseBasis ℤ HD.reference.lattice
  let T := SourceGeometric.ThetaCandidate.CM.data E L HD hb basis hN
  have hp := ProjectiveGeometricThetaPrepared.CM.at_prime E L HD hb basis hN hμ hg hqD
    φ haux hΛ Yref ρ hρ formY hformY hnonzero (hprime q hlarge')
  have hstandard := Intrinsic.ReferenceFrame.CM.IntrinsicReference.standard HD (hprime q hlarge').2
  have hout := SourceGeometric.ThetaRealization.CM.realization E L HD hb hμ basis hN hTateComparison hGeometricTheta
    hg hqD hc46 hConstruction (ElementaryDivisors.CM.lattices hElementaryDivisors q) hstandard
  let W := Classical.choice (Geometric.ThetaWitness.CM.exists_witness T hg hqD hc46 hout)
  obtain ⟨Y, Z, hreduce, _hY, _hZ⟩ := hreductions (0 : Fin 1)
  have he46 : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q] := ElementaryDivisors.CM.lattices hElementaryDivisors q
  let : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke places.count q) :=
    TateComparisonAction.CM.commutativeHeckeRing places.count q he46
  let : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke M.s q) :=
    inferInstanceAs (CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke places.count q))
  have hden := LabeledGoodPrime.CM.denominator_coprime M j Red
  let fullSide := Constructed.IntrinsicReduction.CM.Intrinsic.multiplicative M hM labels (0 : Fin 1)
  obtain ⟨HR, _hR, hbetti, _hint, _hpoly, _hspec, hc⟩ :=
    GivenActionComparison.CM.comparison_for_given_action M hM j hsplit Red labels hlabels
      (0 : Fin 1) hden C ⟨0, hM.1⟩ fullSide hTorsionQuotient Z Y hqD hg hc46 W.action W.realization
      hGeometricComparison he46 (hgeomRed.1 (0 : Fin 1)).1 (hgeomRed.1 (0 : Fin 1)).2 hreduce
  let AM := AlbaneseModel.CM.comparisonModel HD hg j hden
  have hidx := ReferenceActiveIndex.CM.Reference.operators E HD hM.1 hzero W.action fullSide
  have hcmp : Constructed.Comparison.CM.Conclusion AM j.fieldInClosure j.complexClosure j.iota HR
      (fun i => W.action.basis (Neighbor.Types.CM.integralType P.distinguished fullSide i).val) :=
    (congrArg (fun idx => Constructed.Comparison.CM.Conclusion AM
      j.fieldInClosure j.complexClosure j.iota HR idx) hidx).mpr hc
  have hχ := ReferenceActiveIndex.CM.Reference.character E HD hM.1 hzero j labels rfl hactive
  have hextract := SourceGeometric.ThetaArithmetic.CM.Extraction.extraction E L HD hb hμ basis hN
    hLefschetzNormalization hCotangentBundle hCompletedTheta hNormOneApproximation hLocalWeil hPoissonAutomorphy hTateComparison hConstruction hHodgeComparison hHodgeDecomposition hg hqD hc46 W v hv hd
    j hχ fullSide hden he46 HR hbetti hcmp hCMExtraction
  have hactual := hextract ⟨Theta.Weil.CM.finiteWeilInput φ, hp.2.2.2.2⟩
  have href := Source.ConcreteRestriction.CM.reference_extraction E L HD hb hμ basis hN hΛ v
    hHodgeDecomposition hg hqD hc46 hp.1 W φ hp.2.2.2.2 Yref ρ hρ formY hformY θY hθY
    hactual
  apply CofinalExtraction.CM.extraction E v hHodgeDecomposition Nbase N₀ hN₀ hbase X H
    (fun N => (hH N).1) Θ Yref θY href
  intro n hn hdiv
  obtain ⟨_π, f, _hπ, hf, _hs, _hcomp, hθ⟩ := hrestrictions n hn hdiv
  exact ⟨f, hf, hθ⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Projective.CM
