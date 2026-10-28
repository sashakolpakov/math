import OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalPair
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalCoordinatesDifferentiable

/-! # Normal Differentiable -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalDifferentiable.Constructions

noncomputable section

/-! The actual product normal chart is differentiable in both directions
whenever the two factor charts are complex differentiable. -/

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalCoordinatesDifferentiable
open OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalPair.Constructions
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem productChart_mdifferentiable
    {N N' A B G H : Type}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [TopologicalSpace N] [ChartedSpace G N]
    [TopologicalSpace N'] [ChartedSpace H N']
    (c : OpenPartialHomeomorph N A) (d : OpenPartialHomeomorph N' B)
    (hc : c.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, A))
    (hd : d.MDifferentiable 𝓘(ℂ, H) 𝓘(ℂ, B)) :
    (c.prod d).MDifferentiable (𝓘(ℂ, G).prod 𝓘(ℂ, H)) 𝓘(ℂ, A × B) := by
  constructor
  · change MDifferentiableOn (𝓘(ℂ, G).prod 𝓘(ℂ, H)) 𝓘(ℂ, A × B)
      (Prod.map c d) (c.source ×ˢ d.source)
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hc.1.prodMap hd.1
  · change MDifferentiableOn 𝓘(ℂ, A × B) (𝓘(ℂ, G).prod 𝓘(ℂ, H))
      (Prod.map c.symm d.symm) (c.target ×ˢ d.target)
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hc.2.prodMap hd.2

theorem linearCoordinates_mdifferentiable
    {A B : Type}
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    (e : A ≃L[ℂ] B) :
    e.toHomeomorph.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℂ, A) 𝓘(ℂ, B) :=
  ⟨e.contDiff.differentiable one_ne_zero |>.mdifferentiable.mdifferentiableOn,
    e.symm.contDiff.differentiable one_ne_zero |>.mdifferentiable.mdifferentiableOn⟩

variable {M N M' N' E F G H : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace N'] [ChartedSpace H N']
  {p q : ℕ} {u : M → N} {v : M' → N'} {x : M} {y : M'}
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) u x)
  (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair F (Fin q → ℂ) v y)
  (e : ((Fin p → ℂ) × (Fin q → ℂ)) ≃L[ℂ] (Fin (p + q) → ℂ))

theorem productNormalPair_mdifferentiable
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × (Fin p → ℂ)))
    (hQ : Q.ambientChart.MDifferentiable 𝓘(ℂ, H) 𝓘(ℂ, F × (Fin q → ℂ))) :
    (NormalPair.Constructions.productNormalPair P Q e).ambientChart.MDifferentiable
      (𝓘(ℂ, G).prod 𝓘(ℂ, H)) 𝓘(ℂ, (E × F) × (Fin (p + q) → ℂ)) := by
  change (NormalPair.Constructions.productNormalChart P Q e).MDifferentiable _ _
  unfold NormalPair.Constructions.productNormalChart
  rw [OpenPartialHomeomorph.transHomeomorph_eq_trans]
  exact (productChart_mdifferentiable P.ambientChart Q.ambientChart hP hQ).trans
    (linearCoordinates_mdifferentiable (NormalPair.Constructions.productNormalCoordinates (E := E) (F := F) e))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalDifferentiable.Constructions
