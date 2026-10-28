import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AffineProductRank
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Rank
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.NeutralGroup

/-! # Group Rank -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupRank.CM

noncomputable section

/-! The scheme-theoretic order of a finite commutative group is the product
of the orders of its connected and constant factors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Rank.Construction.Schemes
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AffineProductRank
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupDecomposition.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.NeutralGroup.CM

variable {k : Type} [Field k]

theorem tensor_finrank (G H : Grp (Over (Spec (.of k))))
    [IsCommMonObj G.X] [IsCommMonObj H.X] [IsFinite G.X.hom] [IsFinite H.X.hom]
    (z : Spec (.of k)) :
    (G.X ⊗ H.X).hom.finrank z = G.X.hom.finrank z * H.X.hom.finrank z := by
  obtain ⟨R, hR, _, ⟨e⟩⟩ := Picard.Homomorphisms.FiniteHopfPresentation.Construction.finite_commutative_hopfPresentation k G
  obtain ⟨T, hT, _, ⟨f⟩⟩ := Picard.Homomorphisms.FiniteHopfPresentation.Construction.finite_commutative_hopfPresentation k H
  let : Module.Finite k R := hR
  let : Module.Finite k T := hT
  let i : Isogenies.NeighborCounting.AffineProductRank.affine k R ≅ G.X := (Grp.forget _).mapIso e
  let j : Isogenies.NeighborCounting.AffineProductRank.affine k T ≅ H.X := (Grp.forget _).mapIso f
  let ij : G.X ⊗ H.X ≅ Isogenies.NeighborCounting.AffineProductRank.affine k R ⊗ Isogenies.NeighborCounting.AffineProductRank.affine k T := tensorIso i.symm j.symm
  have : IsFinite (Isogenies.NeighborCounting.AffineProductRank.affine k R).hom := Isogenies.NeighborCounting.AffineProductRank.affine_finite k R
  have : IsFinite (Isogenies.NeighborCounting.AffineProductRank.affine k T).hom := Isogenies.NeighborCounting.AffineProductRank.affine_finite k T
  have : IsFinite (Isogenies.NeighborCounting.AffineProductRank.affine k R ⊗ Isogenies.NeighborCounting.AffineProductRank.affine k T).hom :=
    inferInstanceAs (IsFinite (Limits.pullback.fst (Isogenies.NeighborCounting.AffineProductRank.affine k R).hom (Isogenies.NeighborCounting.AffineProductRank.affine k T).hom ≫
      (Isogenies.NeighborCounting.AffineProductRank.affine k R).hom))
  calc
    (G.X ⊗ H.X).hom.finrank z = (Isogenies.NeighborCounting.AffineProductRank.affine k R ⊗ Isogenies.NeighborCounting.AffineProductRank.affine k T).hom.finrank z :=
      AbelianScheme.CartierDuality.Rank.Construction.Schemes.overIso_finrank ij z
    _ = Module.finrank k R * Module.finrank k T := Isogenies.NeighborCounting.AffineProductRank.affine_product_rank k R T z
    _ = G.X.hom.finrank z * H.X.hom.finrank z :=
      congrArg₂ (· * ·) ((Isogenies.NeighborCounting.AffineProductRank.affine_rank k R z).symm.trans (AbelianScheme.CartierDuality.Rank.Construction.Schemes.overIso_finrank i z))
        ((Isogenies.NeighborCounting.AffineProductRank.affine_rank k T z).symm.trans (AbelianScheme.CartierDuality.Rank.Construction.Schemes.overIso_finrank j z))

theorem connected_times_points [IsAlgClosed k]
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X] [IsFinite G.X.hom]
    (z : Spec (.of k)) :
    (GroupDecomposition.CM.neutralPart G).X.hom.finrank z * Nat.card (Over.mk (𝟙 (Spec (.of k))) ⟶ G.X) =
      G.X.hom.finrank z := by
  let : IsFinite (GroupDecomposition.CM.neutralPart G).X.hom := NeutralGroup.CM.neutral_finite G
  let : IsFinite (GroupDecomposition.CM.pointGroup G).X.hom := NeutralGroup.CM.pointGroup_finite G
  let : IsCommMonObj (GroupDecomposition.CM.neutralPart G).X :=
    Picard.PoincareBundle.Kernel.Scheme.kernelGroup_commutative
      (GroupRetraction.CM.componentMap G)
  let : IsCommMonObj (GroupDecomposition.CM.pointGroup G).X := by
    change IsCommMonObj (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k))
      (Over.mk (𝟙 (Spec (.of k))) ⟶ G.X)).X
    infer_instance
  let : Finite (Over.mk (𝟙 (Spec (.of k))) ⟶ G.X) := Picard.Homomorphisms.FiniteGeometricPoints.Construction.finite_overPoints G.X (𝟙 _)
  have hp : (GroupDecomposition.CM.pointGroup G).X.hom.finrank z = Nat.card (Over.mk (𝟙 (Spec (.of k))) ⟶ G.X) :=
    RepresentationTheory.Theta.Geometric.ConstantSchemeDegree.constantScheme_finrank k _ z
  let d : (GroupDecomposition.CM.neutralPart G).X ⊗ (GroupDecomposition.CM.pointGroup G).X ≅ G.X :=
    (Grp.forget _).mapIso (GroupDecomposition.CM.decomposition G)
  exact (congrArg ((GroupDecomposition.CM.neutralPart G).X.hom.finrank z * ·) hp.symm).trans
    ((tensor_finrank (GroupDecomposition.CM.neutralPart G) (GroupDecomposition.CM.pointGroup G) z).symm.trans
      (AbelianScheme.CartierDuality.Rank.Construction.Schemes.overIso_finrank d z))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupRank.CM
