import OAI.AlgebraicTopology.Kunneth.TensorSimplicialForms
import OAI.AlgebraicTopology.Kunneth.SimplexFormCochain

/-! # Simplex Cup Integral -/

namespace OAI.AlgebraicTopology.Kunneth.SimplexCupIntegral

noncomputable section

/-! The actual Alexander--Whitney cup functional on restricted simplex forms. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory Opposite
open scoped Simplicial TensorProduct

namespace Constructions

theorem cochainCast_d (K : SSet.{0}) {n m : ℕ} (h : n = m)
    (c : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of ℂ ℂ)).X n) :
    (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of ℂ ℂ)).d m (m + 1)
      (Products.Cup.cochainCast K (ModuleCat.of ℂ ℂ) h c) =
        Products.Cup.cochainCast K (ModuleCat.of ℂ ℂ) (congrArg (· + 1) h)
          ((Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of ℂ ℂ)).d n (n + 1) c) := by
  subst m
  rfl

theorem cochainCast_trans (K : SSet.{0}) {n m k : ℕ} (h : n = m) (h' : m = k)
    (c : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of ℂ ℂ)).X n) :
    Products.Cup.cochainCast K (ModuleCat.of ℂ ℂ) h' (Products.Cup.cochainCast K (ModuleCat.of ℂ ℂ) h c) =
      Products.Cup.cochainCast K (ModuleCat.of ℂ ℂ) (h.trans h') c := by
  subst m k
  rfl

theorem cochainCast_pullback {K J : SSet.{0}} (f : K ⟶ J) {n m : ℕ} (h : n = m)
    (c : (Cohomology.Singular.Basic.simplicialCochains J (ModuleCat.of ℂ ℂ)).X n) :
    (Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) f).f m (Products.Cup.cochainCast J (ModuleCat.of ℂ ℂ) h c) =
      Products.Cup.cochainCast K (ModuleCat.of ℂ ℂ) h ((Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) f).f n c) := by
  subst m
  rfl

def simplexTensorCup (q n p : ℕ) :
    TensorSimplicialForms.Constructions.SimplexFormTensor q n p →ₗ[ℂ] (Cohomology.Singular.Basic.simplicialCochains Δ[n] (ModuleCat.of ℂ ℂ)).X (q + p) :=
  (Products.Cup.cochainCast Δ[n] (ModuleCat.of ℂ ℂ) (Nat.add_comm p q)).comp
    ((TensorProduct.lift (Products.Cup.cupWithBilinear Δ[n] (LinearMap.mul ℂ ℂ) p q)).comp
      (TensorProduct.map (SimplexFormCochain.Constructions.simplexFormCochain n p)
        ((SimplexFormCochain.Constructions.simplexFormCochain n q).comp (SimplicialForms.Constructions.SimplexClosedForms n q).subtype)))

@[simp] theorem simplexTensorCup_tmul (q n p : ℕ)
    (a : RestrictedForms.Constructions.RestrictedForm (SimplexFormDomain.Constructions.coordinateSimplex n) p) (b : SimplicialForms.Constructions.SimplexClosedForms n q) :
    simplexTensorCup q n p (a ⊗ₜ[ℂ] b) =
      Products.Cup.cochainCast Δ[n] (ModuleCat.of ℂ ℂ) (Nat.add_comm p q)
        (Products.Cup.cupWith Δ[n] (LinearMap.mul ℂ ℂ) (SimplexFormCochain.Constructions.simplexFormCochain n p a)
          (SimplexFormCochain.Constructions.simplexFormCochain n q b.val)) := rfl

theorem simplexTensorCup_d (q n p : ℕ) (a : TensorSimplicialForms.Constructions.SimplexFormTensor q n p) :
    (Cohomology.Singular.Basic.simplicialCochains Δ[n] (ModuleCat.of ℂ ℂ)).d (q + p) (q + p + 1)
      (simplexTensorCup q n p a) =
        simplexTensorCup q n (p + 1) (TensorSimplicialForms.Constructions.simplexFormTensorD q n p a) := by
  have h : ((Cohomology.Singular.Basic.simplicialCochains Δ[n] (ModuleCat.of ℂ ℂ)).d (q + p) (q + p + 1)).hom.comp
        (simplexTensorCup q n p) =
      (simplexTensorCup q n (p + 1)).comp (TensorSimplicialForms.Constructions.simplexFormTensorD q n p) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change (Cohomology.Singular.Basic.simplicialCochains Δ[n] (ModuleCat.of ℂ ℂ)).d (q + p) (q + p + 1)
      (simplexTensorCup q n p (x ⊗ₜ[ℂ] y)) =
        simplexTensorCup q n (p + 1) (TensorSimplicialForms.Constructions.simplexFormTensorD q n p (x ⊗ₜ[ℂ] y))
    rw [simplexTensorCup_tmul, cochainCast_d, Products.Cup.cupWith_coboundary,
      SimplexFormCochain.Constructions.simplexFormCochain_d, SimplexFormCochain.Constructions.simplexFormCochain_d, y.property, map_zero,
      Products.Cup.cupWith_zero_right, smul_zero, add_zero, cochainCast_trans,
      TensorSimplicialForms.Constructions.simplexFormTensorD_tmul, simplexTensorCup_tmul]
    rfl
  exact LinearMap.congr_fun h a

theorem simplexTensorCup_pullback {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (q p : ℕ)
    (a : TensorSimplicialForms.Constructions.SimplexFormTensor q n p) :
    (Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) (SSet.stdSimplex.map f)).f (q + p)
      (simplexTensorCup q n p a) =
        simplexTensorCup q m p (TensorSimplicialForms.Constructions.simplexFormTensorPullback f q p a) := by
  have h : ((Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) (SSet.stdSimplex.map f)).f (q + p)).hom.comp
        (simplexTensorCup q n p) =
      (simplexTensorCup q m p).comp (TensorSimplicialForms.Constructions.simplexFormTensorPullback f q p) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change (Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) (SSet.stdSimplex.map f)).f (q + p)
      (simplexTensorCup q n p (x ⊗ₜ[ℂ] y)) =
      simplexTensorCup q m p (SimplexFormMaps.Constructions.simplexFormPullback f p x ⊗ₜ[ℂ] SimplicialForms.Constructions.simplexClosedFormPullback f q y)
    rw [simplexTensorCup_tmul, cochainCast_pullback, Products.Cup.cupWith_pullback,
      SimplexFormCochain.Constructions.simplexFormCochain_pullback, SimplexFormCochain.Constructions.simplexFormCochain_pullback, simplexTensorCup_tmul]
    rfl
  exact LinearMap.congr_fun h a

def simplexCupIntegral (q p : ℕ) : TensorSimplicialForms.Constructions.SimplexFormTensor q (q + p) p →ₗ[ℂ] ℂ :=
  (Cohomology.Singular.Coefficients.simplicialEvaluation Δ[q + p] (ModuleCat.of ℂ ℂ)
    (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋q + p⦌))).hom.comp (simplexTensorCup q (q + p) p)

theorem simplexTensorCup_evaluation (q n p : ℕ) (a : TensorSimplicialForms.Constructions.SimplexFormTensor q n p)
    (s : Δ[n] _⦋q + p⦌) :
    Cohomology.Singular.Coefficients.simplicialEvaluation Δ[n] (ModuleCat.of ℂ ℂ) s (simplexTensorCup q n p a) =
      simplexCupIntegral q p (TensorSimplicialForms.Constructions.simplexFormTensorPullback (SSet.stdSimplex.objEquiv s) q p a) := by
  have h := congrArg (fun c => Cohomology.Singular.Coefficients.simplicialEvaluation Δ[q + p] (ModuleCat.of ℂ ℂ)
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋q + p⦌)) c)
    (simplexTensorCup_pullback (SSet.stdSimplex.objEquiv s) q p a)
  rw [Cohomology.Singular.Formulas.evaluation_pullback_apply] at h
  have hs : (SSet.stdSimplex.map (SSet.stdSimplex.objEquiv s)).app _
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋q + p⦌)) = s := by
    rw [← SSet.stdSimplex.objEquiv_symm_comp, Category.id_comp, Equiv.symm_apply_apply]
  rw [hs] at h
  exact h

theorem simplexCupIntegral_d (q p : ℕ) :
    (simplexCupIntegral q (p + 1)).comp (TensorSimplicialForms.Constructions.simplexFormTensorD q (q + p + 1) p) =
      TensorSimplicialForms.Constructions.simplexFormTensorDelta q (q + p) p (simplexCupIntegral q p) := by
  apply LinearMap.ext
  intro a
  change Cohomology.Singular.Coefficients.simplicialEvaluation Δ[q + p + 1] (ModuleCat.of ℂ ℂ)
    (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋q + p + 1⦌))
      (simplexTensorCup q (q + p + 1) (p + 1) (TensorSimplicialForms.Constructions.simplexFormTensorD q (q + p + 1) p a)) = _
  rw [← simplexTensorCup_d, Cohomology.Singular.Formulas.evaluation_coboundary_apply, TensorSimplicialForms.Constructions.simplexFormTensorDelta_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [simplexTensorCup_evaluation]
  rfl

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.SimplexCupIntegral
