import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GaussianContraction

/-! # Linear Map Blocks -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.LinearMapBlocks.Construction.LocalSectionLifting

noncomputable section

/-! Extracting the four blocks of a linear differential in product coordinates. -/

variable {R A B C D : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]

def linearMapBlock00 (f : (A × B) →ₗ[R] (C × D)) : A →ₗ[R] C :=
  (LinearMap.fst R C D).comp (f.comp (LinearMap.inl R A B))

def linearMapBlock01 (f : (A × B) →ₗ[R] (C × D)) : B →ₗ[R] C :=
  (LinearMap.fst R C D).comp (f.comp (LinearMap.inr R A B))

def linearMapBlock10 (f : (A × B) →ₗ[R] (C × D)) : A →ₗ[R] D :=
  (LinearMap.snd R C D).comp (f.comp (LinearMap.inl R A B))

theorem linearMap_eq_blocks (f : (A × B) →ₗ[R] (C × D)) (d : B ≃ₗ[R] D)
    (hd : ∀ x, (f (0, x)).2 = d x) :
    f = ComplexGaussian.Construction.LocalSectionLifting.blockDifferential (linearMapBlock00 f) (linearMapBlock01 f) (linearMapBlock10 f) d := by
  apply LinearMap.ext
  intro x
  have hx : x = (x.1, 0) + (0, x.2) := by simp
  have hf := congrArg f hx
  rw [map_add] at hf
  apply Prod.ext
  · change (f x).1 = (f (x.1, 0)).1 + (f (0, x.2)).1
    exact congrArg Prod.fst hf
  · change (f x).2 = (f (x.1, 0)).2 + d x.2
    rw [← hd]
    exact congrArg Prod.snd hf

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.LinearMapBlocks.Construction.LocalSectionLifting
