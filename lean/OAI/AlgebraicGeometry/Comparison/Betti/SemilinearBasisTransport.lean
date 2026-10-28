import Mathlib.LinearAlgebra.Basis.Defs

/-! # Semilinear Basis Transport -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SemilinearBasisTransport.LinearAlgebra

noncomputable section

/-! Transport a genuine module basis along compatible scalar and additive equivalences. -/

variable {R S M N I : Type} [Semiring R] [Semiring S]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]

def basisTransport (b : Module.Basis I R M) (e : R ≃+* S) (f : M ≃+ N)
    (hf : ∀ r m, f (r • m) = e r • f m) : Module.Basis I S N := by
  let : Module R N := Module.compHom N e.toRingHom
  let l : M ≃ₗ[R] N := { f with map_smul' := hf }
  exact (b.map l).mapCoeffs e (fun _ _ => rfl)

theorem basisTransport_apply (b : Module.Basis I R M) (e : R ≃+* S) (f : M ≃+ N)
    (hf : ∀ r m, f (r • m) = e r • f m) (i : I) : basisTransport b e f hf i = f (b i) := by
  let : Module R N := Module.compHom N e.toRingHom
  let l : M ≃ₗ[R] N := { f with map_smul' := hf }
  exact (b.map l).mapCoeffs_apply e (fun _ _ => rfl) i

end

end OAI.AlgebraicGeometry.Comparison.Betti.SemilinearBasisTransport.LinearAlgebra
