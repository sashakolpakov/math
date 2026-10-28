import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapLocalFactor

/-! # Map Factor Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapFactorTransport

noncomputable section

/-! Local linear factorizations are unchanged by compatible comparison maps of their codomains. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {M N P Q : X.Modules}

theorem moduleMapLocalFactor_transport (α : M ⟶ P) (β : N ⟶ P) (ρ : P ⟶ Q)
    (α' : M ⟶ Q) (β' : N ⟶ Q) (hα : α ≫ ρ = α') (hβ : β ≫ ρ = β')
    (U : X.Opens) [IsIso (β.app U)] [IsIso (β'.app U)] :
    MapLocalFactor.moduleMapLocalFactor α β U = MapLocalFactor.moduleMapLocalFactor α' β' U := by
  apply MapLocalFactor.moduleMapLocalFactor_unique
  intro s
  rw [← hβ, ← hα]
  change ρ.app U (β.app U (MapLocalFactor.moduleMapLocalFactor α β U s)) = ρ.app U (α.app U s)
  rw [MapLocalFactor.moduleMapLocalFactor_spec]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapFactorTransport
