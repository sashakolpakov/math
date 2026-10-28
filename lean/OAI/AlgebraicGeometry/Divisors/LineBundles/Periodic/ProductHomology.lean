import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.Exact
import Mathlib.LinearAlgebra.Quotient.Pi

/-! # Product Homology -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.ProductHomology.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual periodic homology of a finite product

Kernels are identified coordinatewise. Under that identification the
boundary image is the product of the individual boundary images, so
the quotient is the actual product of the individual homology modules.
-/

variable {R ι : Type*} [CommRing R] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

theorem periodicPi_comp_zero (φ ψ : ∀ i, M i →ₗ[R] M i)
    (h : ∀ i, (φ i).comp (ψ i) = 0) : (LinearMap.piMap φ).comp (LinearMap.piMap ψ) = 0 := by
  apply LinearMap.ext
  intro m
  funext i
  exact LinearMap.congr_fun (h i) (m i)

def periodicPiKernelEquiv (φ : ∀ i, M i →ₗ[R] M i) :
    (LinearMap.piMap φ).ker ≃ₗ[R] ∀ i, (φ i).ker where
  toFun m i := ⟨m.1 i, by
    change φ i (m.1 i) = 0
    exact congrArg (fun v : ∀ j, M j => v i) m.2⟩
  invFun m := ⟨fun i => (m i).1, funext (fun i => (m i).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem periodicPiBoundary_map (φ ψ : ∀ i, M i →ₗ[R] M i)
    (h : ∀ i, (φ i).comp (ψ i) = 0) :
    (Exact.BundleCycles.periodicBoundaryMap (LinearMap.piMap φ) (LinearMap.piMap ψ)
      (periodicPi_comp_zero φ ψ h)).range.map (periodicPiKernelEquiv φ).toLinearMap =
      Submodule.pi Set.univ (fun i => (Exact.BundleCycles.periodicBoundaryMap (φ i) (ψ i) (h i)).range) := by
  classical
  ext u
  constructor
  · rintro ⟨_, ⟨m, rfl⟩, rfl⟩ i _
    exact ⟨m i, Subtype.ext rfl⟩
  · intro hu
    have hex : ∀ i, ∃ m : M i, Exact.BundleCycles.periodicBoundaryMap (φ i) (ψ i) (h i) m = u i :=
      fun i => hu i (Set.mem_univ i)
    choose m hm using hex
    refine ⟨Exact.BundleCycles.periodicBoundaryMap (LinearMap.piMap φ) (LinearMap.piMap ψ)
      (periodicPi_comp_zero φ ψ h) m, ⟨m, rfl⟩, ?_⟩
    funext i
    exact hm i

def periodicPiHomologyEquiv [Fintype ι] (φ ψ : ∀ i, M i →ₗ[R] M i)
    (h : ∀ i, (φ i).comp (ψ i) = 0) :
    Exact.BundleCycles.periodicHomology (LinearMap.piMap φ) (LinearMap.piMap ψ) (periodicPi_comp_zero φ ψ h) ≃ₗ[R]
      ∀ i, Exact.BundleCycles.periodicHomology (φ i) (ψ i) (h i) := by
  classical
  exact (Submodule.Quotient.equiv _ _ (periodicPiKernelEquiv φ) (periodicPiBoundary_map φ ψ h)).trans
    (Submodule.quotientPi (fun i => (Exact.BundleCycles.periodicBoundaryMap (φ i) (ψ i) (h i)).range))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.ProductHomology.BundleCycles
