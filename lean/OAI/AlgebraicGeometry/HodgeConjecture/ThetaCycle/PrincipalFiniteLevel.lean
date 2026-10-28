import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalColumnDecomposition
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalLocalIntegrality
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RestrictedIntegralNeighborhoods

/-! # Principal Finite Level -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalFiniteLevel.CM

noncomputable section

/-! ThetaCycle: the actual principal congruence tower of the specified ball
lattice is cofinal in the native finite special-unitary topology. -/

open scoped Classical _root_.NumberField _root_.Topology
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary
open OAI.RepresentationTheory.Theta.Adelic.IntegralTopology OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

theorem integer_algebra_map_value {R : Type*} [Ring R] [Algebra ℤ R] (n : ℤ) :
    algebraMap ℤ R n = (n : R) := map_intCast _ n

theorem local_integer_coefficient_factor (F : Type) [Field F] [NumberField F]
    (v : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) (a n c : ℤ) (x : F) :
    algebraMap ℤ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) (a * (n * c)) * RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v x =
      algebraMap ℤ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) n * RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v ((a * c) • x) := by
  have hc (k : ℤ) : algebraMap ℤ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) k = (k : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v) := map_intCast _ k
  rw [map_zsmul]
  simp only [hc, zsmul_eq_mul, Int.cast_mul]
  ring

theorem finite_su_integral_neighborhood (F : Type) [Field F] [NumberField F]
    {d : F} {r : ℕ} (H : (Matrix (Fin r) (Fin r) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (L : OpenSubgroup (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H)) :
    ∃ (J : Finset (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F))
      (V : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, Set (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)))),
      (∀ v, V v ∈ 𝓝 1) ∧ ∀ g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H,
        (∀ v, g v ∈ RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr v)) →
        (∀ v ∈ J, g v ∈ V v) → g ∈ L :=
  RestrictedIntegralNeighborhoods.CM.restricted_integral_neighborhood
    (G := fun v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)))
    (fun v => RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr v))
    (L : Set (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H)) (L.isOpen.mem_nhds L.one_mem)

def FiniteSUIntegerControl (F : Type) [Field F] [NumberField F]
    {d : F} {r : ℕ} (H : (Matrix (Fin r) (Fin r) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (L : OpenSubgroup (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H)) : Prop :=
  ∃ (J : Finset (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F))
      (n : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F → ℤ), (∀ v, n v ≠ 0) ∧
      ∀ g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H, (∀ v, g v ∈ RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F H.val (.inr v)) →
        (∀ v ∈ J, ∃ A : Fin 2 × Fin r × Fin r × Fin 2 → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v),
          (∀ i, A i ∈ v.adicCompletionIntegers F) ∧
          ((g v).val.val - 1, ((g v)⁻¹).val.val - 1) =
            LocalUnitaryNeighborhoods.CM.quadraticMatrixPair (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d)
              (fun i => algebraMap ℤ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (n v) * A i)) → g ∈ L

theorem finite_su_integer_control (F : Type) [Field F] [NumberField F]
    {d : F} {r : ℕ} (H : (Matrix (Fin r) (Fin r) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ)
    (L : OpenSubgroup (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU F H)) : FiniteSUIntegerControl F H L := by
  unfold FiniteSUIntegerControl
  obtain ⟨J, V, hV, hsub⟩ := finite_su_integral_neighborhood F H L
  have hn (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) := LocalUnitaryNeighborhoods.CM.local_unitary_integer_neighborhood F v
    (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d) (RepresentationTheory.Theta.Adelic.SpecialUnitary.specialUnitary (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v))) (V v) (hV v)
  choose n hn0 hlocal using hn
  refine ⟨J, n, hn0, ?_⟩
  intro g hg hcoeff
  apply hsub g hg
  intro v hv
  obtain ⟨A, hA, he⟩ := hcoeff v hv
  exact hlocal v A hA (g v) he

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)

def nativeBallHermitianUnit (B : HeckeCycles.GeometricSource.CM.BallDatum K) :
    (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ)))ˣ :=
  CMGlobalFrames.CM.cmHermitianUnit K δ hδ B.b B.conjugate_b
    (fun hb => (ne_of_lt B.negative) (by simp [hb]))

theorem ball_finite_integer_control (B : HeckeCycles.GeometricSource.CM.BallDatum K)
    (L : OpenSubgroup (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (maximalRealSubfield K) (nativeBallHermitianUnit K δ hδ B))) :
    FiniteSUIntegerControl (maximalRealSubfield K) (nativeBallHermitianUnit K δ hδ B) L :=
  finite_su_integer_control (maximalRealSubfield K)
    (d := QuadraticModel.CM.cmQuadraticParameter K δ hδ) (r := 3) (nativeBallHermitianUnit K δ hδ B) L

theorem lattice_columns_satisfy_local_control (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N : ℕ)
    (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g)
    (J : Finset (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (maximalRealSubfield K)))
    (n : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (maximalRealSubfield K) → ℤ)
    (a : ℤ) (Y : Fin 2 → Fin 3 → HeckeCycles.GeometricSource.CM.Vec K) (hY : ∀ s j, Y s j ∈ B.lattice)
    (ha : ∀ x ∈ B.lattice, ∀ (s : Fin 2) (i : Fin 3),
      IsIntegral ℤ (a • QuadraticCoefficientMaps.CM.cmQuadraticCoefficient K δ hδ hδ0 s (x i)))
    (hcol : ∀ s j, LocalColumnCoordinates.CM.ballColumnDifferences K g s j = (a * ∏ v ∈ J, n v) • Y s j) :
    ∀ v ∈ J,
    let q := RepresentationTheory.Theta.Adelic.RationalSU.rationalLocalSU (maximalRealSubfield K) (nativeBallHermitianUnit K δ hδ B) (.inr v)
      (RationalBallUnitary.CM.rationalBallSU K δ hδ hδ0 B N g hg)
    ∃ A : Fin 2 × Fin 3 × Fin 3 × Fin 2 → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion (maximalRealSubfield K) (.inr v),
      (∀ i, A i ∈ v.adicCompletionIntegers (maximalRealSubfield K)) ∧
      (q.val.val - 1, (q⁻¹).val.val - 1) =
        LocalUnitaryNeighborhoods.CM.quadraticMatrixPair (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (maximalRealSubfield K) (.inr v) (QuadraticModel.CM.cmQuadraticParameter K δ hδ))
          (fun i => algebraMap ℤ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion (maximalRealSubfield K) (.inr v)) (n v) * A i) := by
  let F : Type := maximalRealSubfield K
  let m : ℤ := ∏ v ∈ J, n v
  dsimp only
  intro v hv
  have hdiv : n v ∣ m := Finset.dvd_prod_of_mem n hv
  obtain ⟨c, hc⟩ := hdiv
  change m = n v * c at hc
  let A : Fin 2 × Fin 3 × Fin 3 × Fin 2 → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v) := fun p =>
    RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v)
      ((a * c) • QuadraticCoefficientMaps.CM.cmQuadraticCoefficient K δ hδ hδ0 p.2.2.2 (Y p.1 p.2.2.1 p.2.1))
  have hA (p : Fin 2 × Fin 3 × Fin 3 × Fin 2) : A p ∈ v.adicCompletionIntegers F := by
    apply IntegralLocalCoefficients.CM.integral_scalar_at_every_finite_place F
    rw [mul_smul, smul_comm a c]
    exact (ha (Y p.1 p.2.2.1) (hY p.1 p.2.2.1) p.2.2.2 p.2.1).smul c
  refine ⟨A, hA, ?_⟩
  calc
    _ = LocalUnitaryNeighborhoods.CM.quadraticMatrixPair (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) (QuadraticModel.CM.cmQuadraticParameter K δ hδ))
        (fun p : Fin 2 × Fin 3 × Fin 3 × Fin 2 =>
          algebraMap ℤ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) (a * m) * RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v)
            (QuadraticCoefficientMaps.CM.cmQuadraticCoefficient K δ hδ hδ0 p.2.2.2 (Y p.1 p.2.2.1 p.2.1))) :=
      by simpa only [integer_algebra_map_value] using!
        PrincipalColumnDecomposition.CM.local_ball_column_pair_of_integer_decomposition K δ hδ hδ0 B N g hg (a * m) Y hcol (.inr v)
    _ = _ := by
      apply congrArg (LocalUnitaryNeighborhoods.CM.quadraticMatrixPair _)
      funext p
      rw [hc]
      simpa only [integer_algebra_map_value] using! local_integer_coefficient_factor F (.inr v) a (n v) c
        (QuadraticCoefficientMaps.CM.cmQuadraticCoefficient K δ hδ hδ0 p.2.2.2 (Y p.1 p.2.2.1 p.2.1))

def PrincipalFiniteMembership (B : HeckeCycles.GeometricSource.CM.BallDatum K)
    (L : OpenSubgroup (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (maximalRealSubfield K) (nativeBallHermitianUnit K δ hδ B)))
    (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g) : Prop :=
  RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU (maximalRealSubfield K) (nativeBallHermitianUnit K δ hδ B)
    (RationalBallUnitary.CM.rationalBallSU K δ hδ hδ0 B N g hg) ∈ L

theorem principal_finite_level_cofinal (B : HeckeCycles.GeometricSource.CM.BallDatum K)
    (L : OpenSubgroup (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (maximalRealSubfield K) (nativeBallHermitianUnit K δ hδ B))) :
    ∃ D : ℕ, 0 < D ∧ ∀ N : ℕ, D ∣ N →
      ∀ (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g),
        PrincipalFiniteMembership K δ hδ hδ0 B L N g hg := by
  have hbdata := PrincipalColumnBounds.CM.ball_lattice_standard_basis_denominator K B
  let d : ℤ := hbdata.choose
  have hd : d ≠ 0 := hbdata.choose_spec.1
  have hb := hbdata.choose_spec.2
  have hadata := LatticeCoefficientBounds.CM.ball_lattice_quadratic_coefficients_integral K δ hδ hδ0 B
  let a : ℤ := hadata.choose
  have ha0 : a ≠ 0 := hadata.choose_spec.1
  have ha := hadata.choose_spec.2
  have hIdata := PrincipalLocalIntegrality.CM.exists_principal_local_integral_depth K δ hδ hδ0 B
  let D₁ : ℕ := hIdata.choose
  have hD₁ : 0 < D₁ := hIdata.choose_spec.1
  have hIntegral := hIdata.choose_spec.2
  have hcontrol := ball_finite_integer_control K δ hδ B L
  let J := hcontrol.choose
  let n := hcontrol.choose_spec.choose
  have hn0 := hcontrol.choose_spec.choose_spec.1
  have hsub := hcontrol.choose_spec.choose_spec.2
  let m : ℤ := ∏ v ∈ J, n v
  have hm : m ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ => hn0 v)
  refine ⟨D₁ * (d * (a * m)).natAbs,
    Nat.mul_pos hD₁ (Int.natAbs_pos.mpr (mul_ne_zero hd (mul_ne_zero ha0 hm))), ?_⟩
  intro N hN g hg
  have hN₁ : D₁ ∣ N := dvd_trans ⟨(d * (a * m)).natAbs, rfl⟩ hN
  have hN₂ : (d * (a * m)).natAbs ∣ N :=
    dvd_trans ⟨D₁, Nat.mul_comm _ _⟩ hN
  have hdiv : d * (a * m) ∣ (N : ℤ) := Int.natAbs_dvd_natAbs.mp (by
    simpa only [Int.natAbs_natCast] using hN₂)
  obtain ⟨k, hk⟩ := hdiv
  obtain ⟨Y, hY, hcol⟩ := PrincipalColumnDecomposition.CM.principal_columns_lattice_decomposition K B d (a * m) k hd hb N hk g hg
  unfold PrincipalFiniteMembership
  apply hsub
  · exact fun v => hIntegral N hN₁ g hg v
  · exact lattice_columns_satisfy_local_control K δ hδ hδ0 B N g hg J n a Y hY ha hcol

theorem principal_finite_level_cofinal_explicit (B : HeckeCycles.GeometricSource.CM.BallDatum K)
    (L : OpenSubgroup (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (maximalRealSubfield K) (nativeBallHermitianUnit K δ hδ B))) :
    ∃ D : ℕ, 0 < D ∧ ∀ N : ℕ, D ∣ N →
      ∀ (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g),
        RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU (maximalRealSubfield K) (nativeBallHermitianUnit K δ hδ B)
          (RationalBallUnitary.CM.rationalBallSU K δ hδ hδ0 B N g hg) ∈ L :=
  principal_finite_level_cofinal K δ hδ hδ0 B L

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalFiniteLevel.CM
