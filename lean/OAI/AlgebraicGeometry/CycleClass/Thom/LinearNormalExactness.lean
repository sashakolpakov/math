import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Linear Normal Exactness -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.LinearNormalExactness.Constructions

/-! Rank-nullity identifies the tangent space with the kernel of the normal differential. -/

variable {k W A V : Type*} [Field k]
  [AddCommGroup W] [Module k W] [AddCommGroup A] [Module k A]
  [AddCommGroup V] [Module k V] [FiniteDimensional k A]

theorem ker_eq_range (i : W →ₗ[k] A) (n : A →ₗ[k] V)
    (hi : Function.Injective i) (hn : Function.Surjective n)
    (hz : n.comp i = 0)
    (hd : Module.finrank k W + Module.finrank k V = Module.finrank k A) :
    LinearMap.ker n = LinearMap.range i := by
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro v ⟨w, rfl⟩
    exact LinearMap.congr_fun hz w
  · have hr := n.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hn, finrank_top] at hr
    rw [LinearMap.finrank_range_of_inj hi]
    omega

end OAI.AlgebraicGeometry.CycleClass.Thom.LinearNormalExactness.Constructions
