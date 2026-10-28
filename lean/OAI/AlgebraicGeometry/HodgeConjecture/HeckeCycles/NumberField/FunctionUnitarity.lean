import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.TestProducts
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.IntegralComparison
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PureFunctionExt
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FunctionAction

/-! # Function Unitarity -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.FunctionUnitarity.CM.GlobalPairing

/-! The global sesquilinear form is actual Haar integration in rational
coordinates and the product of normalized local Haar pairings on pure tests. -/

open scoped Classical _root_.NumberField
open Filter
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz
open OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Restricted

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def productForm : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N →ₗ[ℂ]
    RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N →ₗ⋆[ℂ] RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N where
  toFun f :=
    { toFun h := TestProducts.CM.product F N f h
      map_add' h k := by
        apply Subtype.ext
        funext x
        exact (congrArg (fun z => f.val x * z) (star_add (h.val x) (k.val x))).trans (mul_add _ _ _)
      map_smul' c h := by
        apply Subtype.ext
        funext x
        change f.val x * star (c * h.val x) = star c * (f.val x * star (h.val x))
        rw [star_mul]
        ring }
  map_add' f h := by
    apply LinearMap.ext
    intro k
    apply Subtype.ext
    funext x
    exact add_mul _ _ _
  map_smul' c f := by
    apply LinearMap.ext
    intro h
    apply Subtype.ext
    funext x
    exact mul_assoc _ _ _

def pairing : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N →ₗ[ℂ] RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N →ₗ⋆[ℂ] ℂ where
  toFun f := (LocalIntegral.CM.globalIntegral F N).comp (productForm F N f)
  map_add' f h := by
    apply LinearMap.ext
    intro k
    change LocalIntegral.CM.globalIntegral F N (productForm F N (f + h) k) = _
    rw [map_add, LinearMap.add_apply, map_add]
    rfl
  map_smul' c f := by
    apply LinearMap.ext
    intro h
    change LocalIntegral.CM.globalIntegral F N (productForm F N (c • f) h) = _
    rw [map_smul, LinearMap.smul_apply, map_smul]
    rfl

theorem pure_pairing
    (f h : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v)
    (hh : ∀ᶠ v in cofinite, h v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) :
    pairing F N (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf))
      (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) h hh)) =
      ∏ᶠ v, LocalPairing.CM.pairing F N v (f v) (h v) := by
  change LocalIntegral.CM.globalIntegral F N
    (TestProducts.CM.product F N _ _) = _
  rw [TestProducts.CM.pure_product]
  unfold LocalIntegral.CM.globalIntegral
  rw [Finite.FunctionAction.CM.FunctionalDescent.function_pure]
  rfl

theorem rational_pairing
    (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Finite.AdelicTestCoordinates.CM.Index F N)) :
    pairing F N (Finite.AdelicTestCoordinates.CM.equivalence F N f)
      (Finite.AdelicTestCoordinates.CM.equivalence F N h) =
      Finite.FiniteOscillator.CM.integralPairing f h := by
  let p : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Finite.AdelicTestCoordinates.CM.Index F N) :=
    ⟨fun x => f.val x * star (h.val x), (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mpr
      ⟨((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mp f.property).1.mul
        (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mp h.property).1.comp star),
        (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_hasCompactSupport f).mul_right⟩⟩
  exact IntegralComparison.CM.integral F N p

def pulled (U : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N ≃ₗ[ℂ] RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N) :
    RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N →ₗ[ℂ] RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N →ₗ⋆[ℂ] ℂ where
  toFun f := (pairing F N (U f)).comp U.toLinearMap
  map_add' f h := by
    apply LinearMap.ext
    intro k
    change pairing F N (U (f + h)) (U k) = _
    rw [map_add, map_add]
    rfl
  map_smul' c f := by
    apply LinearMap.ext
    intro h
    change pairing F N (U (c • f)) (U h) = _
    rw [map_smul, map_smul]
    rfl

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.FunctionUnitarity.CM.GlobalPairing

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.FunctionUnitarity.CM

/-! Local unitarity implies global Haar unitarity on the actual finite
Schwartz functions through the proved pure-product pairing formula. -/

open scoped Classical _root_.NumberField
open Filter
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Restricted

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
  {G : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F → Type*} [∀ v, Group (G v)]
  (K : ∀ v, Subgroup (G v))
  (ρ : ∀ v, G v →* (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N ≃ₗ[ℂ]
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N))
  (hρ : ∀ᶠ v in cofinite, ∀ g ∈ K v, ρ v g (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v)
  (hu : ∀ v g f h, LocalPairing.CM.pairing F N v (ρ v g f) (ρ v g h) =
    LocalPairing.CM.pairing F N v f h)

include hu in
theorem unitary (g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K) (φ ψ : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N) :
    GlobalPairing.pairing F N
      (Finite.FunctionAction.CM.functionAction F N K ρ hρ g φ)
      (Finite.FunctionAction.CM.functionAction F N K ρ hρ g ψ) =
      GlobalPairing.pairing F N φ ψ := by
  have h := Finite.PureFunctionExt.CM.Sesquilinear.ext F N
    (GlobalPairing.pulled F N (Finite.FunctionAction.CM.functionAction F N K ρ hρ g))
    (GlobalPairing.pairing F N) (by
      intro f k hf hk
      change GlobalPairing.pairing F N
        (Finite.FunctionAction.CM.functionAction F N K ρ hρ g
          (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf)))
        (Finite.FunctionAction.CM.functionAction F N K ρ hρ g
          (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) k hk))) = _
      rw [Finite.FunctionAction.CM.intertwines, Finite.FunctionAction.CM.intertwines,
        RestrictedTensorExpansion.CM.action_pure, RestrictedTensorExpansion.CM.action_pure,
        GlobalPairing.pure_pairing, GlobalPairing.pure_pairing]
      apply finprod_congr
      intro v
      exact hu v (g v) (f v) (k v))
  exact congrArg (fun L : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N →ₗ[ℂ]
    RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N →ₗ⋆[ℂ] ℂ => L φ ψ) h

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.FunctionUnitarity.CM

end

end OAI
