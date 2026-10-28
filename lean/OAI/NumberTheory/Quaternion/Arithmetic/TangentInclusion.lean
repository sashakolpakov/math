import OAI.NumberTheory.Quaternion.Arithmetic.Complement
import OAI.NumberTheory.Quaternion.Arithmetic.NonzeroTangentProjection
import OAI.NumberTheory.Quaternion.Arithmetic.PrimeBlockDecomposition
import OAI.NumberTheory.Quaternion.Arithmetic.SinglePlaceNondiscrete

/-! # Tangent Inclusion -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.TangentInclusion

noncomputable section

section

/-! A nondiscrete single-place arithmetic projection yields a nonzero
tangent projection in the simultaneous local matrix representation. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set _root_.Topology

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {ι : Type*}

local instance arithmeticTangentProjectionCharZero (w : HeightOneSpectrum (𝓞 F)) :
    CharZero (w.adicCompletion F) := Algebra.charZero_of_charZero F _

theorem arithmetic_complement_nonzero_tangent
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    (v₀ : HeightOneSpectrum (𝓞 F)) (v : ι → HeightOneSpectrum (𝓞 F))
    (hv : Function.Injective v) (haway : ∀ j, Sum.inr (v j) ∉ S) (i : ι)
    [∀ j, Algebra (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) ((v j).adicCompletion F)]
    {D : Type*} [NormedRing D] [NormedAlgebra (v₀.adicCompletion F) D] [CompleteSpace D]
    (f : (∀ j, Matrix (Fin n) (Fin n) ((v j).adicCompletion F)) →ₐ[TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)] D)
    (hf : IsClosedEmbedding f)
    (hnd : ¬ IsDiscrete (Closure.localArithmeticSubgroup G (insert (Sum.inr (v i)) S) (Sum.inr (v i)) :
      Set (LocalAdeles.LocalPoints G (Sum.inr (v i))))) :
    ∃ a : ∀ j, Matrix (Fin n) (Fin n) ((v j).adicCompletion F),
      f a ∈ LocalSubgroup.primeLocalTangentSpan v₀
        ((((Complement.arithmeticComplementEmbedding G S v hv haway i).range.topologicalClosure).toSubmonoid.map
          ((PrimeBlockDecomposition.finiteMatrixProductHom G v).comp (IntegralComplement.insertIntegralComplement G v i))).map f.toMonoidHom) ∧
      a i ≠ 0 := by
  let R := (Complement.arithmeticComplementEmbedding G S v hv haway i).range
  let H := R.topologicalClosure
  let e := (PrimeBlockDecomposition.finiteMatrixProductHom G v).comp (IntegralComplement.insertIntegralComplement G v i)
  have he : Continuous e :=
    (IsClosedEmbedding.piMap (fun j => IntegralCompact.localPoints_closedEmbedding G (Sum.inr (v j)))).continuous.comp
      (IntegralComplement.insertIntegralComplement_continuous G v i)
  have hd : ¬ IsDiscrete (H.map
      (MonoidHom.snd (IntegralComplement.integralComplement G v i) (LocalAdeles.LocalPoints G (Sum.inr (v i)))) :
      Set (LocalAdeles.LocalPoints G (Sum.inr (v i)))) := by
    intro hdis
    apply hnd
    rw [← Complement.arithmeticComplementEmbedding_projection_range G S v hv haway i]
    exact hdis.mono (Subgroup.map_mono R.le_topologicalClosure)
  let π := Pi.evalRingHom (fun j => Matrix (Fin n) (Fin n) ((v j).adicCompletion F)) i
  apply NonzeroTangentProjection.compact_projection_has_nonzero_tangent v₀ f hf π (continuous_apply i) e he
    (MatrixOpenness.localMatrixMonoidHom G (v i)) (IntegralCompact.localPoints_closedEmbedding G (Sum.inr (v i))).injective
    _ H R.isClosed_topologicalClosure hd
  intro x
  change MatrixOpenness.localMatrixMonoidHom G (v i) (IntegralComplement.insertIntegralComplement G v i x i) = _
  rw [IntegralComplement.insertIntegralComplement_self]

theorem arithmetic_complement_nonzero_tangent_of_volume
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    (v₀ : HeightOneSpectrum (𝓞 F)) (v : ι → HeightOneSpectrum (𝓞 F))
    (hv : Function.Injective v) (haway : ∀ j, Sum.inr (v j) ∉ S) (i : ι)
    [∀ j, Algebra (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) ((v j).adicCompletion F)]
    {D : Type*} [NormedRing D] [NormedAlgebra (v₀.adicCompletion F) D] [CompleteSpace D]
    (f : (∀ j, Matrix (Fin n) (Fin n) ((v j).adicCompletion F)) →ₐ[TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)] D)
    (hf : IsClosedEmbedding f)
    (hnoncompact : ∃ w : LocalAdeles.Place F, w ∈ S ∧ ¬ CompactSpace (LocalAdeles.LocalPoints G w))
    (hvolume : CompactQuotientProjection.QuotientHasInvariantProbability
      (Ambient.arithmeticAmbientSubgroup G S {⟨Sum.inr (v i), haway i⟩})) :
    ∃ a : ∀ j, Matrix (Fin n) (Fin n) ((v j).adicCompletion F),
      f a ∈ LocalSubgroup.primeLocalTangentSpan v₀
        ((((Complement.arithmeticComplementEmbedding G S v hv haway i).range.topologicalClosure).toSubmonoid.map
          ((PrimeBlockDecomposition.finiteMatrixProductHom G v).comp (IntegralComplement.insertIntegralComplement G v i))).map f.toMonoidHom) ∧
      a i ≠ 0 := by
  apply arithmetic_complement_nonzero_tangent G S v₀ v hv haway i f hf
  exact SinglePlaceNondiscrete.localArithmetic_single_not_discrete G S ⟨Sum.inr (v i), haway i⟩ hnoncompact hvolume

end

/-! Nonzero directions from single-place arithmetic groups persist in
any closed simultaneous local subgroup containing their rational points. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set _root_.Topology

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {ι : Type*}

theorem arithmeticComplementClosure_map_le (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Finset (LocalAdeles.Place F)) (v : ι → HeightOneSpectrum (𝓞 F))
    (hv : Function.Injective v) (haway : ∀ j, Sum.inr (v j) ∉ S) (i : ι)
    (J : Subgroup (∀ j, LocalAdeles.LocalPoints G (Sum.inr (v j))))
    (hJ : IsClosed (J : Set (∀ j, LocalAdeles.LocalPoints G (Sum.inr (v j)))))
    (hΓ : ∀ g : Groups.sIntegralPoints G (insert (Sum.inr (v i)) (S : Set (LocalAdeles.Place F))),
      (fun j => LocalAdeles.diagonalLocal G (Sum.inr (v j)) g.val) ∈ J) :
    (Complement.arithmeticComplementEmbedding G S v hv haway i).range.topologicalClosure.map
      (IntegralComplement.insertIntegralComplement G v i) ≤ J := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply Subgroup.topologicalClosure_minimal
  · rintro x ⟨g, rfl⟩
    have he : IntegralComplement.insertIntegralComplement G v i (Complement.arithmeticComplementEmbedding G S v hv haway i g) =
        (fun j => LocalAdeles.diagonalLocal G (Sum.inr (v j)) g.val) :=
      funext fun j => Complement.arithmeticComplementEmbedding_coordinate G S v hv haway i j g
    change IntegralComplement.insertIntegralComplement G v i (Complement.arithmeticComplementEmbedding G S v hv haway i g) ∈ J
    exact he.symm ▸ hΓ g
  · exact hJ.preimage (IntegralComplement.insertIntegralComplement_continuous G v i)

theorem closed_arithmetic_product_tangent_projection_nonzero
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    (v₀ : HeightOneSpectrum (𝓞 F)) (v : ι → HeightOneSpectrum (𝓞 F))
    (hv : Function.Injective v) (haway : ∀ j, Sum.inr (v j) ∉ S) (i : ι)
    [∀ j, Algebra (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) ((v j).adicCompletion F)]
    {D : Type*} [NormedRing D] [NormedAlgebra (v₀.adicCompletion F) D] [CompleteSpace D]
    (f : (∀ j, Matrix (Fin n) (Fin n) ((v j).adicCompletion F)) →ₐ[TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)] D)
    (hf : IsClosedEmbedding f)
    (J : Subgroup (∀ j, LocalAdeles.LocalPoints G (Sum.inr (v j))))
    (hJ : IsClosed (J : Set (∀ j, LocalAdeles.LocalPoints G (Sum.inr (v j)))))
    (hΓ : ∀ g : Groups.sIntegralPoints G (insert (Sum.inr (v i)) (S : Set (LocalAdeles.Place F))),
      (fun j => LocalAdeles.diagonalLocal G (Sum.inr (v j)) g.val) ∈ J)
    (hnoncompact : ∃ w : LocalAdeles.Place F, w ∈ S ∧ ¬ CompactSpace (LocalAdeles.LocalPoints G w))
    (hvolume : CompactQuotientProjection.QuotientHasInvariantProbability
      (Ambient.arithmeticAmbientSubgroup G S {⟨Sum.inr (v i), haway i⟩})) :
    ∃ a : ∀ j, Matrix (Fin n) (Fin n) ((v j).adicCompletion F),
      f a ∈ LocalSubgroup.primeLocalTangentSpan v₀
        ((J.toSubmonoid.map (PrimeBlockDecomposition.finiteMatrixProductHom G v)).map f.toMonoidHom) ∧ a i ≠ 0 := by
  obtain ⟨a, ha, hai⟩ := arithmetic_complement_nonzero_tangent_of_volume
    G S v₀ v hv haway i f hf hnoncompact hvolume
  refine ⟨a, ?_, hai⟩
  have hle := arithmeticComplementClosure_map_le G S v hv haway i J hJ hΓ
  have hm : ((Complement.arithmeticComplementEmbedding G S v hv haway i).range.topologicalClosure).toSubmonoid.map
      ((PrimeBlockDecomposition.finiteMatrixProductHom G v).comp (IntegralComplement.insertIntegralComplement G v i)) ≤
        J.toSubmonoid.map (PrimeBlockDecomposition.finiteMatrixProductHom G v) := by
    rintro x ⟨g, hg, rfl⟩
    exact ⟨IntegralComplement.insertIntegralComplement G v i g, hle ⟨g, hg, rfl⟩, rfl⟩
  have hm' : (((Complement.arithmeticComplementEmbedding G S v hv haway i).range.topologicalClosure).toSubmonoid.map
      ((PrimeBlockDecomposition.finiteMatrixProductHom G v).comp (IntegralComplement.insertIntegralComplement G v i))).map f.toMonoidHom ≤
        (J.toSubmonoid.map (PrimeBlockDecomposition.finiteMatrixProductHom G v)).map f.toMonoidHom := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y, hm hy, rfl⟩
  exact (Submodule.span_mono (tangentConeAt_mono hm')) ha

end

end OAI.NumberTheory.Quaternion.Arithmetic.TangentInclusion
