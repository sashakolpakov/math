import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeutralFunctor
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalizableSubgroup
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks

/-! # Neutral Subgroup -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeutralSubgroup.CM

noncomputable section

/-! A finite subgroup's connected factor inherits a spanning character
presentation from an actual multiplicative connected ambient factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupDecomposition.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.NeutralGroup.CM

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  (A B : Grp (Over (Spec (.of k)))) [IsFinite A.X.hom] [IsFinite B.X.hom]
  [IsCommMonObj A.X] [IsCommMonObj B.X]

theorem spanning_presentation (f : B ⟶ A) [Mono f.hom.hom]
    (I : Type u) [CommGroup I]
    (e : HeckeCycles.Finite.GroupDecomposition.CM.neutralPart A ≅ (hopfSpec (.of k)).obj (.op (CommHopfAlgCat.of k (MonoidAlgebra k I)))) :
    ∃ R : CommHopfAlgCat k, Module.Finite k R ∧
      Nonempty ((hopfSpec (.of k)).obj (.op R) ≅ HeckeCycles.Finite.GroupDecomposition.CM.neutralPart B) ∧
      Submodule.span k (Set.range (GroupLike.val (R := k) (A := R))) = ⊤ := by
  let : IsFinite (HeckeCycles.Finite.GroupDecomposition.CM.neutralPart B).X.hom := HeckeCycles.Finite.NeutralGroup.CM.neutral_finite B
  let : IsCommMonObj (HeckeCycles.Finite.GroupDecomposition.CM.neutralPart B).X :=
    Picard.PoincareBundle.Kernel.Scheme.kernelGroup_commutative (HeckeCycles.Finite.GroupRetraction.CM.componentMap B)
  let c := NeutralFunctor.CM.map B A f ≫ e.hom
  let : Mono (NeutralFunctor.CM.map B A f).hom.hom := NeutralFunctor.CM.map_mono B A f
  let : Mono c.hom.hom := inferInstanceAs
    (Mono ((NeutralFunctor.CM.map B A f).hom.hom ≫ e.hom.hom.hom))
  let : IsSeparated ((hopfSpec (.of k)).obj (.op (CommHopfAlgCat.of k (MonoidAlgebra k I)))).X.hom :=
    inferInstanceAs (IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra k I)))))
  let : IsClosedImmersion c.hom.hom.left := AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.closedSubgroupOfFiniteMono c.hom.hom
  exact DiagonalizableSubgroup.CM.spanning_presentation_of_closed_embedding k (HeckeCycles.Finite.GroupDecomposition.CM.neutralPart B) I c

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeutralSubgroup.CM
