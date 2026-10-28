import OAI.NumberTheory.Quaternion.Arithmetic.SimultaneousNormClosure
import OAI.NumberTheory.Quaternion.Arithmetic.ProductCurveTangents

/-! # Norm Trace Tangents -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.NormTraceTangents

noncomputable section

/-! Trace directions, with independent local scalar multiples, lie
in the tangent cone of any closed set containing the rational points. -/

open scoped Classical _root_.Matrix.Norms.Operator
open _root_.Matrix Set Filter _root_.Topology

variable {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E]
  [FiniteDimensional F E] [IsGalois F E] {ι : Type*} [Fintype ι] [Nonempty ι]
  {κ : Type*} [NontriviallyNormedField κ] {K A : ι → Type*}
  [∀ i, NontriviallyNormedField (K i)] [∀ i, Algebra F (K i)] [∀ i, Algebra κ (K i)]
  [∀ i, NormedCommRing (A i)] [∀ i, Nontrivial (A i)] [∀ i, Algebra F (A i)]
  [∀ i, Algebra κ (A i)] [∀ i, NormedAlgebra (K i) (A i)]
  [∀ i, IsScalarTower F (K i) (A i)] [∀ i, IsScalarTower κ (K i) (A i)]
  [∀ i, CompleteSpace (K i)] [∀ i, CompleteSpace (A i)] [∀ i, FiniteDimensional (K i) (A i)]
  {n : ℕ}

theorem norm_trace_local_multiples_mem_tangentCone (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Matrix (Fin n) (Fin n) F) (B : ArithmeticGroups.Lattices.Algebraic.SL n E) (m : Fin n → ℤ)
    (hLie : MappedWeightCurves.integerWeightMatrix B m ∈
      ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap F E)))
    (hpoly : ∀ u : Eˣ, ∃ p : Polynomial E, Polynomial.aeval (S.map (algebraMap F E)) p =
      (B : Matrix (Fin n) (Fin n) E) * Matrix.diagonal (fun i => ((u ^ m i : Eˣ) : E)) *
        ((B⁻¹ : ArithmeticGroups.Lattices.Algebraic.SL n E) : Matrix (Fin n) (Fin n) E))
    (f : ∀ i, E →ₐ[F] A i) (a : E) (b : ∀ i, K i)
    (he : ∀ i, Continuous (algebraMap κ (K i)))
    (hdense : DenseRange (fun r : F => fun i => algebraMap F (K i) r))
    (C : Set (∀ i, Matrix (Fin n) (Fin n) (A i))) (hC : IsClosed C)
    (hrational : ∀ g : G.RationalPoints,
      (fun i => (PolynomialGaloisNorm.matrixPointsHom G (RingHom.id F) g).map (algebraMap F (A i))) ∈ C) :
    (fun i => b i • (GaloisTraceMatrix.fieldTraceMatrix (F := F) (a • MappedWeightCurves.integerWeightMatrix B m)).map
      (algebraMap F (A i))) ∈ tangentConeAt κ C 1 := by
  let q := fun i (t : K i) => LocalGaloisNormCurve.localGaloisNormCurve (f i) B a m (t * b i)
  let y := fun i => b i • (GaloisTraceMatrix.fieldTraceMatrix (F := F) (a • MappedWeightCurves.integerWeightMatrix B m)).map
    (algebraMap F (A i))
  have hq (i : ι) : HasDerivAt (q i) (y i) 0 := by
    have h := (LocalGaloisNormCurve.localGaloisNormCurve_hasDerivAt (K := K i) (f i) B a m).scomp_of_eq 0
      ((hasDerivAt_id (0 : K i)).mul_const (b i)) (zero_mul (b i)).symm
    simpa only [q, y, Function.comp_def, one_mul, id_eq] using! h
  have hm := SimultaneousNormClosure.simultaneousNormCurve_eventually_mem_closed (K := K) G S B m hLie hpoly
    f a hdense C hC hrational
  have ht : Tendsto (fun t : ∀ i, K i => fun i => t i * b i)
      (𝓝 (0 : ∀ i, K i)) (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [Pi.zero_apply, zero_mul] using
      ((continuous_apply i).continuousAt (x := (0 : ∀ i, K i))).tendsto.mul
        (tendsto_const_nhds (x := b i))
  have hmem : ∀ᶠ t in 𝓝 (0 : ∀ i, K i), (fun i => q i (t i)) ∈ C := ht hm
  have hc := ProductCurveTangents.product_curve_derivatives_mem_tangentCone he q y hq hmem
  have hz : (fun i => q i 0) = 1 := by
    funext i
    simp only [q, zero_mul, LocalGaloisNormCurve.localGaloisNormCurve_zero, Pi.one_apply]
  exact hz ▸ hc

end

end OAI.NumberTheory.Quaternion.Arithmetic.NormTraceTangents
