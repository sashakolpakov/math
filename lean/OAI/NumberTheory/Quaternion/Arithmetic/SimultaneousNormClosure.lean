import OAI.NumberTheory.Quaternion.Arithmetic.RationalNormCurveValues
import OAI.NumberTheory.Quaternion.Arithmetic.LocalGaloisNormCurve
import OAI.NumberTheory.Quaternion.Arithmetic.DenseParameterClosure

/-! # Simultaneous Norm Closure -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.SimultaneousNormClosure

noncomputable section

/-! Weak approximation on the scalar parameters puts the local norm
curves into every closed set containing the diagonal rational points. -/

open scoped Classical _root_.Matrix.Norms.Operator
open _root_.Matrix Set Filter _root_.Topology

variable {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E]
  [FiniteDimensional F E] [IsGalois F E] {ι : Type*} [Fintype ι] [Nonempty ι]
  {K A : ι → Type*} [∀ i, NontriviallyNormedField (K i)] [∀ i, Algebra F (K i)]
  [∀ i, NormedCommRing (A i)] [∀ i, Nontrivial (A i)] [∀ i, Algebra F (A i)]
  [∀ i, NormedAlgebra (K i) (A i)] [∀ i, IsScalarTower F (K i) (A i)]
  [∀ i, CompleteSpace (K i)] [∀ i, CompleteSpace (A i)] [∀ i, FiniteDimensional (K i) (A i)]
  {n : ℕ}

def simultaneousNormCurve (f : ∀ i, E →ₐ[F] A i) (B : ArithmeticGroups.Lattices.Algebraic.SL n E) (a : E) (m : Fin n → ℤ)
    (t : ∀ i, K i) : ∀ i, Matrix (Fin n) (Fin n) (A i) :=
  fun i => LocalGaloisNormCurve.localGaloisNormCurve (f i) B a m (t i)

theorem simultaneousNormCurve_eventually_mem_closed (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (S : Matrix (Fin n) (Fin n) F) (B : ArithmeticGroups.Lattices.Algebraic.SL n E) (m : Fin n → ℤ)
    (hLie : MappedWeightCurves.integerWeightMatrix B m ∈
      ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap F E)))
    (hpoly : ∀ u : Eˣ, ∃ p : Polynomial E, Polynomial.aeval (S.map (algebraMap F E)) p =
      (B : Matrix (Fin n) (Fin n) E) * Matrix.diagonal (fun i => ((u ^ m i : Eˣ) : E)) *
        ((B⁻¹ : ArithmeticGroups.Lattices.Algebraic.SL n E) : Matrix (Fin n) (Fin n) E))
    (f : ∀ i, E →ₐ[F] A i) (a : E)
    (hdense : DenseRange (fun r : F => fun i => algebraMap F (K i) r))
    (C : Set (∀ i, Matrix (Fin n) (Fin n) (A i))) (hC : IsClosed C)
    (hrational : ∀ g : G.RationalPoints,
      (fun i => (PolynomialGaloisNorm.matrixPointsHom G (RingHom.id F) g).map (algebraMap F (A i))) ∈ C) :
    ∀ᶠ t in 𝓝 (0 : ∀ i, K i), simultaneousNormCurve f B a m t ∈ C := by
  let U : Set (∀ i, K i) := {t | ∀ i, ∀ σ : E ≃ₐ[F] E, IsUnit (1 + t i • f i (σ a))}
  have hUopen : IsOpen U := by
    have he : U = ⋂ i, (fun t : ∀ i, K i => t i) ⁻¹'
        {x : K i | ∀ σ : E ≃ₐ[F] E, IsUnit (1 + x • f i (σ a))} := by
      ext t
      simp only [U, mem_ofPred_eq, mem_iInter, mem_preimage]
    rw [he]
    exact isOpen_iInter_of_finite (fun i =>
      (LocalGaloisNormCurve.localGaloisNormCurve_unitDomain_isOpen (K := K i) (f i) a).preimage (continuous_apply i))
  have hUzero : (0 : ∀ i, K i) ∈ U := by
    intro i σ
    simp only [Pi.zero_apply, zero_smul, add_zero, isUnit_one]
  filter_upwards [hUopen.mem_nhds hUzero] with t ht
  have hcont : ContinuousAt (simultaneousNormCurve f B a m) t := by
    apply continuousAt_pi.mpr
    intro i
    exact (LocalGaloisNormCurve.localGaloisNormCurve_continuousAt (K := K i) (f i) B a m (ht i)).comp
      (f := fun t : ∀ i, K i => t i) (continuous_apply i).continuousAt
  apply DenseParameterClosure.dense_parameters_mem_closed hdense hC hcont (hUopen.mem_nhds ht)
  intro r hr
  let i₀ : ι := Classical.choice inferInstance
  have hunit : IsUnit (1 + algebraMap F E r * a) :=
    RationalNormCurveValues.global_affine_isUnit_of_local (K := K i₀) (f i₀) a r (hr i₀ 1)
  obtain ⟨u, hu⟩ := hunit
  obtain ⟨g, hg⟩ := RationalNormCurveValues.simultaneous_rational_norm_curve_values (K := K) G S B m hLie hpoly f a r u hu
  have he : simultaneousNormCurve f B a m (fun i => algebraMap F (K i) r) =
      fun i => (PolynomialGaloisNorm.matrixPointsHom G (RingHom.id F) g).map (algebraMap F (A i)) := funext hg
  rw [he]
  exact hrational g

end

end OAI.NumberTheory.Quaternion.Arithmetic.SimultaneousNormClosure
