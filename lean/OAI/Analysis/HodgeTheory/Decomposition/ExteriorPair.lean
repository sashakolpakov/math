import OAI.Analysis.HodgeTheory.Decomposition.CovectorPair
import OAI.Analysis.HodgeTheory.Decomposition.MetricFiber

/-! # Exterior Pair -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions

noncomputable section

section

/-! The metric Hermitian pairing on genuine alternating covectors and its
invariance under real tangent isometries. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Exterior powers preserve the real metric under a tangent isometry. -/
theorem exteriorMap_inner (n : ℕ) (L : E ≃ₗᵢ[ℝ] F) (x y : ⋀[ℝ]^n E) :
    inner ℝ (exteriorPower.map n L.toLinearEquiv.toLinearMap x)
      (exteriorPower.map n L.toLinearEquiv.toLinearMap y) = inner ℝ x y := by
  have hbilin :
      (innerₗ (⋀[ℝ]^n F)).compl₁₂ (exteriorPower.map n L.toLinearEquiv.toLinearMap)
        (exteriorPower.map n L.toLinearEquiv.toLinearMap) = innerₗ (⋀[ℝ]^n E) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    change inner ℝ (exteriorPower.map n L.toLinearEquiv.toLinearMap (exteriorPower.ιMulti ℝ n v))
      (exteriorPower.map n L.toLinearEquiv.toLinearMap (exteriorPower.ιMulti ℝ n w)) =
      inner ℝ (exteriorPower.ιMulti ℝ n v) (exteriorPower.ιMulti ℝ n w)
    simp only [exteriorPower.map_apply_ιMulti, exteriorPower.inner_ιMulti_ιMulti,
      Function.comp_apply, LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe,
      L.inner_map_map]
  exact congrArg (fun B : (⋀[ℝ]^n E) →ₗ[ℝ] (⋀[ℝ]^n E) →ₗ[ℝ] ℝ => B x y) hbilin

/-- The actual induced map on exterior powers, with its inverse. -/
def exteriorIsometryEquiv (n : ℕ) (L : E ≃ₗᵢ[ℝ] F) : (⋀[ℝ]^n E) ≃ₗᵢ[ℝ] (⋀[ℝ]^n F) :=
  LinearEquiv.isometryOfInner
    { toLinearMap := exteriorPower.map n L.toLinearEquiv.toLinearMap
      invFun := exteriorPower.map n L.symm.toLinearEquiv.toLinearMap
      left_inv := fun x => by
        change ((exteriorPower.map n L.symm.toLinearEquiv.toLinearMap).comp
          (exteriorPower.map n L.toLinearEquiv.toLinearMap)) x = x
        have hL : L.symm.toLinearEquiv.toLinearMap.comp L.toLinearEquiv.toLinearMap =
            LinearMap.id := by ext u; exact L.symm_apply_apply u
        rw [← exteriorPower.map_comp, hL, exteriorPower.map_id]
        rfl
      right_inv := fun x => by
        change ((exteriorPower.map n L.toLinearEquiv.toLinearMap).comp
          (exteriorPower.map n L.symm.toLinearEquiv.toLinearMap)) x = x
        have hL : L.toLinearEquiv.toLinearMap.comp L.symm.toLinearEquiv.toLinearMap =
            LinearMap.id := by ext u; exact L.apply_symm_apply u
        rw [← exteriorPower.map_comp, hL, exteriorPower.map_id]
        rfl }
    (exteriorMap_inner n L)

/-- The intrinsic Hermitian pairing on complex-valued alternating covectors. -/
def formMetricPair (n : ℕ) (f g : DifferentialForms.Manifold.Basic.FormValue E n) : ℂ :=
  CovectorPair.Constructions.covectorInner (DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv E n f) (DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv E n g)

theorem formMetricPair_symm (n : ℕ) (f g : DifferentialForms.Manifold.Basic.FormValue E n) :
    star (formMetricPair n g f) = formMetricPair n f g :=
  CovectorPair.Constructions.covectorInner_symm _ _

theorem formMetricPair_nonneg (n : ℕ) (f : DifferentialForms.Manifold.Basic.FormValue E n) :
    0 ≤ (formMetricPair n f f).re := CovectorPair.Constructions.covectorInner_nonneg _

theorem formMetricPair_definite (n : ℕ) (f : DifferentialForms.Manifold.Basic.FormValue E n) (hf : formMetricPair n f f = 0) :
    f = 0 := by
  apply (DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv E n).injective
  rw [map_zero]
  exact CovectorPair.Constructions.covectorInner_definite _ hf

/-- Pullback by an actual tangent isometry preserves the induced form pairing. -/
theorem formMetricPair_pullback (n : ℕ) (L : E ≃ₗᵢ[ℝ] F) (f g : DifferentialForms.Manifold.Basic.FormValue F n) :
    formMetricPair n (f.compContinuousLinearMap L.toContinuousLinearEquiv.toContinuousLinearMap)
      (g.compContinuousLinearMap L.toContinuousLinearEquiv.toContinuousLinearMap) =
      formMetricPair n f g := by
  unfold formMetricPair
  rw [DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv_pullback, DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv_pullback]
  exact CovectorPair.Constructions.covectorInner_pullback_isometry (exteriorIsometryEquiv n L) _ _

end

/-! A real normed copy for an arbitrary positive symmetric metric. This
allows differentiation of induced covector metrics without changing the
original coordinate norm or manifold topology. -/

section Copy
variable (E : Type*) [AddCommGroup E] [Module ℝ E]

structure RealMetricFiber (_ : InnerProductSpace.Core ℝ E) where
  val : E

variable (h : InnerProductSpace.Core ℝ E)

def realMetricFiberUnderlying : RealMetricFiber E h ≃ E where
  toFun := RealMetricFiber.val
  invFun := RealMetricFiber.mk
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance realMetricFiberAddCommGroup : AddCommGroup (RealMetricFiber E h) :=
  (realMetricFiberUnderlying E h).addCommGroup

private def realMetricFiberAddEquiv : RealMetricFiber E h ≃+ E where
  toEquiv := realMetricFiberUnderlying E h
  map_add' _ _ := rfl

instance realMetricFiberModule : Module ℝ (RealMetricFiber E h) :=
  (realMetricFiberAddEquiv E h).module ℝ

def realMetricFiberEquiv : RealMetricFiber E h ≃ₗ[ℝ] E :=
  (realMetricFiberAddEquiv E h).linearEquiv ℝ

instance realMetricFiberCore : InnerProductSpace.Core ℝ (RealMetricFiber E h) where
  inner u v := h.inner u.val v.val
  conj_inner_symm u v := h.conj_inner_symm u.val v.val
  re_inner_nonneg u := h.re_inner_nonneg u.val
  add_left u v w := h.add_left u.val v.val w.val
  smul_left u v r := h.smul_left u.val v.val r
  definite u hu := by
    have hv : u.val = 0 := h.definite u.val hu
    cases u
    cases hv
    rfl

instance realMetricFiberNormed : NormedAddCommGroup (RealMetricFiber E h) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance realMetricFiberInner : InnerProductSpace ℝ (RealMetricFiber E h) :=
  InnerProductSpace.ofCore _

instance realMetricFiberFiniteDimensional [FiniteDimensional ℝ E] : FiniteDimensional ℝ (RealMetricFiber E h) :=
  (realMetricFiberEquiv E h).symm.finiteDimensional

end Copy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[instance_reducible] def positiveBilinearCore (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = B v u) (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) : InnerProductSpace.Core ℝ E where
  inner u v := B u v
  conj_inner_symm u v := hB v u
  re_inner_nonneg u := by
    by_cases hu : u = 0
    · subst u
      simp
    · exact (hpos u hu).le
  add_left u v w := by simp only [map_add, add_apply]
  smul_left u v r := by simp only [map_smul, smul_apply, smul_eq_mul, RCLike.conj_to_real]
  definite u hu := by
    by_contra hne
    exact (hpos u hne).ne' hu

variable [FiniteDimensional ℝ E]

def realMetricFiberContinuousEquiv (h : InnerProductSpace.Core ℝ E) : RealMetricFiber E h ≃L[ℝ] E :=
  (realMetricFiberEquiv E h).toContinuousLinearEquiv

theorem realMetricFiber_inner (h : InnerProductSpace.Core ℝ E) (u v : RealMetricFiber E h) :
    inner ℝ u v = h.inner (realMetricFiberContinuousEquiv h u) (realMetricFiberContinuousEquiv h v) := rfl

end

end OAI.Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions
