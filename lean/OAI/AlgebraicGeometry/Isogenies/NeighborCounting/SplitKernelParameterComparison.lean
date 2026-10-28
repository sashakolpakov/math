import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitSubgroupDetection
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteFlatKernelTransport
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.SubgroupModel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.TestComparison

/-! # Split Kernel Parameter Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitKernelParameterComparison

noncomputable section

/-! For an actually split finite etale generic block, equality of the
original rational-point predicates identifies the constructed kernel
with the entire original parameterized subgroup on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitSubgroupDetection
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

universe u

theorem pointPullbackGroupEquiv_parameter_membership {S T : Scheme.{u}}
    (f : T ⟶ S) (G : Grp (Over S)) (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X (Over.mk f))
    (a : Over.mk f ⟶ G.X) :
    GroupPointBaseChange.pointPullbackGroupEquiv f G a ∈
      (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G (Over.mk f) F).points (Over.mk (𝟙 T)) (𝟙 _) ↔
    a ∈ F.points (Over.mk f) (𝟙 _) :=
  AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterizePoint_membership G F (𝟙 (Over.mk f)) a (𝟙 _)

theorem splitKernel_eq_parameterSubgroup {S : Scheme.{u}} {k I : Type u} [Field k]
    (f : Spec (.of k) ⟶ S) (G : Grp (Over S))
    [IsCommMonObj ((Over.pullback f).obj G.X)]
    [IsFinite ((Over.pullback f).obj G.X).hom] [Etale ((Over.pullback f).obj G.X).hom]
    (e : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I ≅ (Over.pullback f).obj G.X)
    (K : Kernel.Properties.FiniteFlatKernel ((Over.pullback f).obj G.X))
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X (Over.mk f)) (R : F.Model)
    (h : ∀ a : Over.mk f ⟶ G.X,
      (∃ b : Over.mk (𝟙 (Spec (.of k))) ⟶ K.carrier,
        b ≫ K.inclusion = GroupPointBaseChange.pointPullbackGroupEquiv f G a) ↔
      a ∈ F.points (Over.mk f) (𝟙 _)) :
    Kernel.Base.fixedKernelFamily (P := Over.mk (𝟙 (Spec (.of k)))) K.inclusion =
      AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G (Over.mk f) F := by
  apply SplitSubgroupDetection.eq_of_split_rational_points e (K.relativeModel _)
    (AbelianScheme.IsogenyQuotient.Parameter.SubgroupModel.Construction.relativeSubgroupOverParameter_model G (Over.mk f) F R)
  ext b
  obtain ⟨a, rfl⟩ := (GroupPointBaseChange.pointPullbackGroupEquiv f G).surjective b
  exact (h a).trans (pointPullbackGroupEquiv_parameter_membership f G F a).symm

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitKernelParameterComparison
