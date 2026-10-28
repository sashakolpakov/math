import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ActionDescent

/-! # Action From Pullback Maps -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionFromPullbackMaps

noncomputable section

/-! Actual descended coefficient morphisms whose pullbacks recover an
integral action satisfy all group and ring identities. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S T : Scheme.{0}} {g : ℕ} {R : Type} [CommRing R]

def integralActionOfPullbackMaps (u : T ⟶ S) [Flat u] [Surjective u] [LocallyOfFinitePresentation u]
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R (A.pullback u))
    (f : R → (A.scheme ⟶ A.scheme)) (hf : ∀ r, (Over.pullback u).map (f r) = ρ.map r) :
    AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A where
  map := f
  preservesGroup r := by
    have : IsMonHom ((Over.pullback u).map (f r)) := by
      rw [hf]
      exact ρ.preservesGroup r
    exact ActionDescent.isMonHom_of_faithful_map (Over.pullback u) (f r)
  map_zero := by
    apply (Over.pullback u).map_injective
    rw [hf, (Over.pullback u).map_one]
    exact ρ.map_zero
  map_one := by
    apply (Over.pullback u).map_injective
    rw [hf, (Over.pullback u).map_id]
    exact ρ.map_one
  map_add r s := by
    apply (Over.pullback u).map_injective
    rw [hf, (Over.pullback u).map_mul, hf, hf]
    exact ρ.map_add r s
  map_mul r s := by
    apply (Over.pullback u).map_injective
    rw [hf, (Over.pullback u).map_comp, hf, hf]
    exact ρ.map_mul r s

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionFromPullbackMaps
