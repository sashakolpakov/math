import OAI.RepresentationTheory.Theta.Geometric.CechDimensionComparison
import OAI.RepresentationTheory.Theta.Geometric.CechFieldBaseChange
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineCoverModel

/-! # Constant Fiber Dimension -/

namespace OAI.RepresentationTheory.Theta.Geometric.ConstantFiberDimension

noncomputable section

/-! Any affine Cech cover on a field base change computes the original
H1 dimension. This applies to a line bundle trivial on the actual fiber. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem geometricCech_H1_finrank_cover_baseChange
    {X Y S T : Scheme.{u}} [IsAffine S] [IsAffine T] [X.IsSeparated] [Y.IsSeparated]
    [Nontrivial Γ(T, ⊤)] (hS : IsField Γ(S, ⊤))
    (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S) (hp : IsPullback f ρ π g)
    (M : X.Modules) [M.IsQuasicoherent]
    [((Scheme.Modules.pullback f).obj M).IsQuasicoherent] (N : Y.Modules)
    (e : N ≅ (Scheme.Modules.pullback f).obj M)
    {I J : Type u} [LinearOrder I] [Finite I] [LinearOrder J]
    (U : I → X.Opens) (V : J → Y.Opens) (hU : IsOpenCover U) (hV : IsOpenCover V)
    (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ j, IsAffineOpen (V j)) :
    Module.finrank Γ(T, ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex ρ N V).sc' 0 1 2).homology =
      Module.finrank Γ(S, ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).sc' 0 1 2).homology := by
  have : IsAffineHom f := MorphismProperty.of_isPullback (P := @IsAffineHom) hp.flip inferInstance
  have hUf : IsOpenCover (fun i => f ⁻¹ᵁ U i) := by
    apply IsOpenCover.mk
    rw [← f.preimage_iSup, hU.iSup_eq_top]
    rfl
  have hc := CechDimensionComparison.orderedBaseCech_H1_finrank_cover ρ ((Scheme.Modules.pullback f).obj M)
    V (fun i => f ⁻¹ᵁ U i) hV hUf haV (fun i => (haU i).preimage f)
  exact (CechDimensionComparison.orderedBaseCech_H1_finrank_iso ρ e V).trans (hc.trans
    (CechFieldBaseChange.geometricCech_H1_finrank_field_baseChange hS f π ρ g hp M U
      (fun n i => AlgebraicGeometry.SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U haU n i.1)))

end

end OAI.RepresentationTheory.Theta.Geometric.ConstantFiberDimension
