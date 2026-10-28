import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FilteredModuleFg
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NoetherNormalizationDimension
import Mathlib.RingTheory.Finiteness.Subalgebra

/-! # Filtered Algebra Upper Growth -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FilteredAlgebraUpperGrowth.Construction

noncomputable section

/-! A finite module over a polynomial subalgebra has at most its polynomial growth. -/

open _root_.MvPolynomial

variable {K B : Type*} [Field K] [CommRing B] [Algebra K B]

theorem finiteSubmodule_bounded_in_exhaustive_filtration
    (F : ℕ → Submodule K B) (hF : Monotone F) (hex : ∀ x : B, ∃ n, x ∈ F n)
    (W : Submodule K B) (hW : W.FG) : ∃ n : ℕ, W ≤ F n := by
  classical
  obtain ⟨s, hs⟩ := hW
  choose b hb using fun x : s => hex x.1
  refine ⟨s.attach.sup b, ?_⟩
  rw [← hs, Submodule.span_le]
  intro x hx
  exact hF (Finset.le_sup (f := b) (s.mem_attach ⟨x, hx⟩)) (hb ⟨x, hx⟩)

theorem exists_finite_polynomialModuleFrame
    {τ : Type*} (φ : MvPolynomial τ K →ₐ[K] B) (hfin : φ.Finite) :
    ∃ T : Submodule K B, T.FG ∧ 1 ≤ T ∧ ∀ x : B, ∃ n : ℕ,
      x ∈ PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) (fun i => φ (MvPolynomial.X i)) n * T := by
  classical
  let A := MvPolynomial τ K
  let : Algebra A B := φ.toRingHom.toAlgebra
  have : Module.Finite A B := hfin
  obtain ⟨r, m, hm⟩ := Module.Finite.exists_fin (R := A) (M := B)
  let T : Submodule K B := Submodule.span K (insert 1 (Set.range m))
  have hT : T.FG := Submodule.fg_span ((Set.finite_range m).insert 1)
  have hT1 : (1 : Submodule K B) ≤ T :=
    Submodule.one_le.mpr (Submodule.subset_span (Set.mem_insert 1 _))
  let w := fun i : τ => φ (MvPolynomial.X i)
  have he : MvPolynomial.aeval w = φ := (MvPolynomial.aeval_unique φ).symm
  have hmono : Monotone (fun n => PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) w n * T) :=
    fun _ _ h => Submodule.smul_mono (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece_mono w h) le_rfl
  have hcoeff (a : A) : φ a ∈ PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) w a.totalDegree :=
    (PolynomialFilteredAlgebra.Construction.mem_polynomialFilteredPiece w _ _).mpr ⟨a, le_rfl, congrArg (fun f => f a) he⟩
  refine ⟨T, hT, hT1, fun x => ?_⟩
  have hx : x ∈ Submodule.span A (Set.range m) := by rw [hm]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
      refine ⟨0, ?_⟩
      have h₁ : (1 : B) ∈ PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) w 0 := by
        simpa using PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece_algebraMap w 0 (1 : K)
      simpa only [one_mul] using Submodule.mul_mem_mul h₁
        (show y ∈ T from Submodule.subset_span (Set.mem_insert_of_mem 1 hy))
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
      obtain ⟨n, hn⟩ := hx
      obtain ⟨m, hm⟩ := hy
      exact ⟨max n m, Submodule.add_mem _ (hmono (le_max_left _ _) hn)
        (hmono (le_max_right _ _) hm)⟩
  | smul a x _ hx =>
      obtain ⟨n, hn⟩ := hx
      refine ⟨a.totalDegree + n, ?_⟩
      change φ a * x ∈ _
      have hh := Submodule.mul_mem_mul (hcoeff a) hn
      rw [← mul_assoc] at hh
      exact (Submodule.smul_mono (FilteredModuleFg.Construction.polynomialFilteredPiece_mul_le w a.totalDegree n)
        (le_refl T)) hh

theorem polynomialFilteredPiece_upper_growth_of_finite
    {σ τ : Type*} [Fintype σ] [Fintype τ]
    (φ : MvPolynomial τ K →ₐ[K] B) (hfin : φ.Finite) (v : σ → B) :
    ∃ c D : ℕ, 0 < c ∧ ∀ n : ℕ,
      Module.finrank K (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) v n) ≤
        D * (n * c + 1) ^ Fintype.card τ := by
  classical
  obtain ⟨T, hT, hT1, hex⟩ := exists_finite_polynomialModuleFrame φ hfin
  let w := fun i : τ => φ (MvPolynomial.X i)
  let W : Submodule K B := Submodule.span K (insert 1 (Set.range v))
  have hW : W.FG := Submodule.fg_span ((Set.finite_range v).insert 1)
  have hW1 : (1 : Submodule K B) ≤ W :=
    Submodule.one_le.mpr (Submodule.subset_span (Set.mem_insert 1 _))
  have hmono : Monotone (fun n => PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) w n * T) :=
    fun _ _ h => Submodule.smul_mono (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece_mono w h) le_rfl
  obtain ⟨c, hc⟩ := finiteSubmodule_bounded_in_exhaustive_filtration _ hmono hex (W * T) (hW.mul hT)
  have hc' : W * T ≤ PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) w (c + 1) * T :=
    hc.trans (hmono (Nat.le_succ c))
  have : Module.Finite K T := Module.Finite.iff_fg.mpr hT
  have hfinite (n : ℕ) : Module.Finite K (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) w n * T) :=
    Module.Finite.of_surjective (Submodule.mulMap' _ T) (Submodule.mulMap'_surjective _ T)
  refine ⟨c + 1, Module.finrank K T, Nat.zero_lt_succ _, fun n => ?_⟩
  have hsub : PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) v n ≤ PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece w (n * (c + 1)) * T := by
    calc
      PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) v n ≤ W ^ n :=
        FilteredModuleFg.Construction.polynomialFilteredPiece_le_pow v W hW1
          (fun i => Submodule.subset_span (Set.mem_insert_of_mem 1 ⟨i, rfl⟩)) n
      _ = W ^ n * 1 := (mul_one _).symm
      _ ≤ W ^ n * T := Submodule.smul_mono le_rfl hT1
      _ ≤ PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece w (n * (c + 1)) * T := FilteredModuleFg.Construction.submodule_pow_mul_le_filtered w W T (c + 1) hc' n
  have : Module.Finite K (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) w (n * (c + 1)) * T) := hfinite _
  calc
    Module.finrank K (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) v n) ≤
        Module.finrank K ↥(PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) w (n * (c + 1)) * T) := Submodule.finrank_mono hsub
    _ ≤ Module.finrank K (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece w (n * (c + 1))) * Module.finrank K T :=
      FilteredModuleFg.Construction.finite_submodule_product_finrank_le (K := K)
        (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) w (n * (c + 1))) T
    _ ≤ (n * (c + 1) + 1) ^ Fintype.card τ * Module.finrank K T :=
      Nat.mul_le_mul_right _ (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece_finrank_le τ w _)
    _ = Module.finrank K T * (n * (c + 1) + 1) ^ Fintype.card τ := Nat.mul_comm _ _

universe u

theorem polynomialFilteredPiece_krullDimension_upper_growth
    (K B : Type u) [Field K] [CommRing B] [Nontrivial B]
    [Algebra K B] [Algebra.FiniteType K B]
    {σ : Type*} [Fintype σ] (v : σ → B) :
    ∃ g : ℕ, ringKrullDim B = (g : WithBot ℕ∞) ∧ ∃ c D : ℕ, 0 < c ∧ ∀ n : ℕ,
      Module.finrank K (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) v n) ≤ D * (n * c + 1) ^ g := by
  obtain ⟨g, φ, _, hfin, hdim⟩ := NoetherNormalizationDimension.Construction.noetherNormalization_krullDimension K B
  obtain ⟨c, D, hc, hb⟩ := polynomialFilteredPiece_upper_growth_of_finite φ hfin v
  refine ⟨g, hdim, c, D, hc, fun n => ?_⟩
  simpa only [Fintype.card_fin] using hb n

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FilteredAlgebraUpperGrowth.Construction
