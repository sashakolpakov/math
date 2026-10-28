import OAI.AlgebraicGeometry.Comparison.Betti.HigherSmoothSymbols
import OAI.AlgebraicGeometry.Comparison.Betti.AlternatingCovectors

/-! # Symbol Pointwise -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.SymbolPointwise

noncomputable section

section

/-! Pointwise exterior-covector description of every realized algebraic symbol. -/

open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {A : Type*} [CommRing A] [Algebra ℂ A]
  (φ : A →ₐ[ℂ] C(M, ℂ))
  (hφ : ∀ a : A, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (φ a))

local instance tangentNormedGroup (x : M) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (NormedAddCommGroup E)

local instance tangentNormedSpace (x : M) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (NormedSpace ℝ E)

/-- The one-covector is the actual exterior derivative, evaluated at the given point. -/
def functionCovector (a : A) (x : M) : TangentSpace 𝓘(ℝ, E) x [⋀^Fin 1]→L[ℝ] ℂ :=
  Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (FormRealization.zeroFormMap φ hφ a) x

theorem smoothSymbol_covectors : ∀ (n : ℕ) (a : Fin (n + 1) → A) (x : M),
    HigherSmoothSymbols.smoothSymbol φ hφ n a x =
      AlternatingCovectors.Smooth.iteratedCovectorWedge n (φ (a 0) x) (fun i => functionCovector φ hφ (a i.succ) x) := by
  intro n
  induction n with
  | zero => intro a x; rfl
  | succ n ih =>
      intro a x
      change AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (HigherSmoothSymbols.smoothSymbol φ hφ n (Fin.init a) x)
          (functionCovector φ hφ (a (Fin.last (n + 1))) x) =
        AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge
          (AlternatingCovectors.Smooth.iteratedCovectorWedge n (φ (a 0) x)
            (Fin.init (fun i : Fin (n + 1) => functionCovector φ hφ (a i.succ) x)))
          (functionCovector φ hφ (a (Fin.last n).succ) x)
      rw [ih]
      have hvec : (fun i : Fin n => functionCovector φ hφ (Fin.init a i.succ) x) =
          Fin.init (fun i : Fin (n + 1) => functionCovector φ hφ (a i.succ) x) := by
        funext i
        change functionCovector φ hφ (a i.succ.castSucc) x =
          functionCovector φ hφ (a i.castSucc.succ) x
        rw [Fin.succ_castSucc]
      rw [hvec]
      rfl

theorem functionCovector_add (a b : A) (x : M) :
    functionCovector φ hφ (a + b) x = functionCovector φ hφ a x + functionCovector φ hφ b x := by
  unfold functionCovector
  rw [map_add, map_add]
  rfl

theorem functionCovector_smul (c : ℂ) (a : A) (x : M) :
    functionCovector φ hφ (c • a) x = c • functionCovector φ hφ a x := by
  unfold functionCovector
  rw [map_smul, map_smul]
  rfl

/-- The scalar factors in Leibniz are actual evaluations at the same point. -/
theorem functionCovector_mul (a b : A) (x : M) :
    functionCovector φ hφ (a * b) x =
      φ a x • functionCovector φ hφ b x + φ b x • functionCovector φ hφ a x := by
  unfold functionCovector
  rw [FormRealization.d_zeroFormMap_mul]
  rfl

theorem functionCovector_constant (c : ℂ) (x : M) :
    functionCovector φ hφ (algebraMap ℂ A c) x = 0 := by
  have hc : algebraMap ℂ A c = c • (1 : A) :=
    ((Algebra.smul_def c (1 : A)).trans (mul_one _)).symm
  rw [hc, functionCovector_smul]
  change c • (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (FormRealization.zeroFormMap φ hφ 1) x) = 0
  rw [FormRealization.d_zeroFormMap_one]
  ext v
  exact mul_zero c

/-- Every repeated algebraic differential vanishes in the actual smooth realization. -/
theorem smoothSymbol_repeated {n : ℕ} (a : Fin (n + 1) → A)
    (i j : Fin n) (hij : i ≠ j) (ha : a i.succ = a j.succ) :
    HigherSmoothSymbols.smoothSymbol φ hφ n a = 0 := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  rw [smoothSymbol_covectors]
  exact AlternatingCovectors.Smooth.iteratedCovectorWedge_repeated _ _ i j hij (congrArg (fun b => functionCovector φ hφ b x) ha)

end

/-! Every defining algebraic form relation vanishes in genuine smooth forms. -/

open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {A : Type*} [CommRing A] [Algebra ℂ A]
  (φ : A →ₐ[ℂ] C(M, ℂ))
  (hφ : ∀ a : A, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (φ a))

attribute [local instance] tangentNormedGroup tangentNormedSpace

theorem covectors_update_zero {n : ℕ} (a : Fin (n + 1) → A) (b : A) (x : M) :
    (fun i : Fin n => functionCovector φ hφ (Function.update a 0 b i.succ) x) =
      (fun i => functionCovector φ hφ (a i.succ) x) := by
  funext i
  rw [Function.update_of_ne i.succ_ne_zero]

theorem covectors_update_succ {n : ℕ} (a : Fin (n + 1) → A) (i : Fin n) (b : A) (x : M) :
    (fun j : Fin n => functionCovector φ hφ (Function.update a i.succ b j.succ) x) =
      Function.update (fun j => functionCovector φ hφ (a j.succ) x) i (functionCovector φ hφ b x) := by
  change (fun b => functionCovector φ hφ b x) ∘ Fin.tail (Function.update a i.succ b) =
    Function.update ((fun b => functionCovector φ hφ b x) ∘ Fin.tail a) i (functionCovector φ hφ b x)
  rw [Fin.tail_update_succ, Function.comp_update]

theorem smoothSymbol_add {n : ℕ} (a : Fin (n + 1) → A) (i : Fin (n + 1)) (b c : A) :
    HigherSmoothSymbols.smoothSymbol φ hφ n (Function.update a i (b + c)) =
      HigherSmoothSymbols.smoothSymbol φ hφ n (Function.update a i b) + HigherSmoothSymbols.smoothSymbol φ hφ n (Function.update a i c) := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  change HigherSmoothSymbols.smoothSymbol φ hφ n (Function.update a i (b + c)) x =
    HigherSmoothSymbols.smoothSymbol φ hφ n (Function.update a i b) x + HigherSmoothSymbols.smoothSymbol φ hφ n (Function.update a i c) x
  simp only [smoothSymbol_covectors]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [covectors_update_zero, Function.update_self, map_add, ContinuousMap.add_apply]
    exact AlternatingCovectors.Smooth.iteratedCovectorWedge_add_coeff _ _ _
  · simp only [covectors_update_succ, Function.update_of_ne (Ne.symm j.succ_ne_zero), functionCovector_add]
    exact AlternatingCovectors.Smooth.iteratedCovectorWedge_add_slot _ _ _ _ _

theorem smoothSymbol_smul {n : ℕ} (a : Fin (n + 1) → A) (i : Fin (n + 1)) (c : ℂ) (b : A) :
    HigherSmoothSymbols.smoothSymbol φ hφ n (Function.update a i (c • b)) =
      c • HigherSmoothSymbols.smoothSymbol φ hφ n (Function.update a i b) := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  change HigherSmoothSymbols.smoothSymbol φ hφ n (Function.update a i (c • b)) x =
    c • HigherSmoothSymbols.smoothSymbol φ hφ n (Function.update a i b) x
  simp only [smoothSymbol_covectors]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [covectors_update_zero, Function.update_self, map_smul, ContinuousMap.smul_apply, smul_eq_mul]
    exact AlternatingCovectors.Smooth.iteratedCovectorWedge_smul_coeff _ _ _
  · simp only [covectors_update_succ, Function.update_of_ne (Ne.symm j.succ_ne_zero), functionCovector_smul]
    exact AlternatingCovectors.Smooth.iteratedCovectorWedge_smul_slot _ _ _ _ _

theorem smoothSymbol_leibniz {n : ℕ} (a : Fin (n + 1) → A) (i : Fin n) (b c : A) :
    HigherSmoothSymbols.smoothSymbol φ hφ n (Function.update a i.succ (b * c)) =
      HigherSmoothSymbols.smoothSymbol φ hφ n (Function.update (Function.update a 0 (a 0 * b)) i.succ c) +
        HigherSmoothSymbols.smoothSymbol φ hφ n (Function.update (Function.update a 0 (a 0 * c)) i.succ b) := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  change HigherSmoothSymbols.smoothSymbol φ hφ n (Function.update a i.succ (b * c)) x =
    HigherSmoothSymbols.smoothSymbol φ hφ n (Function.update (Function.update a 0 (a 0 * b)) i.succ c) x +
      HigherSmoothSymbols.smoothSymbol φ hφ n (Function.update (Function.update a 0 (a 0 * c)) i.succ b) x
  simp only [smoothSymbol_covectors, covectors_update_succ, covectors_update_zero,
    Function.update_of_ne (Ne.symm i.succ_ne_zero), Function.update_self,
    functionCovector_mul, map_mul, ContinuousMap.mul_apply]
  erw [AlternatingCovectors.Smooth.iteratedCovectorWedge_add_slot, AlternatingCovectors.Smooth.iteratedCovectorWedge_smul_slot,
    AlternatingCovectors.Smooth.iteratedCovectorWedge_smul_slot,
    mul_comm (φ (a 0) x) (φ b x), mul_comm (φ (a 0) x) (φ c x),
    AlternatingCovectors.Smooth.iteratedCovectorWedge_smul_coeff, AlternatingCovectors.Smooth.iteratedCovectorWedge_smul_coeff]
  rfl

theorem smoothSymbol_constant {n : ℕ} (a : Fin (n + 1) → A) (i : Fin n) (c : ℂ) :
    HigherSmoothSymbols.smoothSymbol φ hφ n (Function.update a i.succ (algebraMap ℂ A c)) = 0 := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  rw [smoothSymbol_covectors, covectors_update_succ, functionCovector_constant]
  exact AlternatingCovectors.Smooth.iteratedCovectorWedge_zero_slot _ _ _

/-- The complete presentation, including differential closure, is respected. -/
theorem rawSmoothMap_relation_zero {n : ℕ} {r : Algebraic.Forms.RawForm A n}
    (hr : Algebraic.Forms.FormRelation A n r) : HigherSmoothSymbols.rawSmoothMap φ hφ n r = 0 := by
  induction hr with
  | add n a i b c =>
      rw [map_sub, map_sub, HigherSmoothSymbols.rawSmoothMap_symbol, HigherSmoothSymbols.rawSmoothMap_symbol, HigherSmoothSymbols.rawSmoothMap_symbol,
        smoothSymbol_add]
      abel
  | smul n a i c b =>
      rw [map_sub, map_smul, HigherSmoothSymbols.rawSmoothMap_symbol, HigherSmoothSymbols.rawSmoothMap_symbol, smoothSymbol_smul, sub_self]
  | leibniz n a i b c =>
      rw [map_sub, map_sub, HigherSmoothSymbols.rawSmoothMap_symbol, HigherSmoothSymbols.rawSmoothMap_symbol, HigherSmoothSymbols.rawSmoothMap_symbol,
        smoothSymbol_leibniz]
      abel
  | constant n a i c => rw [HigherSmoothSymbols.rawSmoothMap_symbol, smoothSymbol_constant]
  | alternating n a i j hij ha => rw [HigherSmoothSymbols.rawSmoothMap_symbol, smoothSymbol_repeated φ hφ a i j hij ha]
  | differential hr ih => rw [HigherSmoothSymbols.rawSmoothMap_d, ih, map_zero]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.SymbolPointwise
