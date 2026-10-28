import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor

/-! # Cech Dimension Comparison -/

namespace OAI.RepresentationTheory.Theta.Geometric.CechDimensionComparison

noncomputable section

/-! The actual H1 dimension of an ordered affine Cech cover is unchanged
by a line-bundle isomorphism or by changing the affine cover. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem orderedBaseCech_H1_finrank_iso {X S : Scheme.{u}} (π : X ⟶ S)
    {M N : X.Modules} (e : M ≅ N) {I : Type u} [LinearOrder I] (U : I → X.Opens) :
    Module.finrank Γ(S, ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).sc' 0 1 2).homology =
      Module.finrank Γ(S, ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π N U).sc' 0 1 2).homology := by
  let f := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} Γ(S, ⊤))
    (ComplexShape.up ℕ) 0 1 2).mapIso ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U).mapIso e)
  exact (ShortComplex.homologyMapIso f).toLinearEquiv.finrank_eq

theorem orderedBaseCech_H1_finrank_cover {X S : Scheme.{u}} [X.IsSeparated]
    (π : X ⟶ S) (M : X.Modules) [M.IsQuasicoherent]
    {I J : Type u} [LinearOrder I] [LinearOrder J]
    (U : I → X.Opens) (V : J → X.Opens) (hU : IsOpenCover U) (hV : IsOpenCover V)
    (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ j, IsAffineOpen (V j)) :
    Module.finrank Γ(S, ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).sc' 0 1 2).homology =
      Module.finrank Γ(S, ⊤) ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M V).sc' 0 1 2).homology := by
  let := AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule π M 1
  let eU := (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M U).homologyIsoSc' 0 1 2 (by simp) (by simp)
  let eV := (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π M V).homologyIsoSc' 0 1 2 (by simp) (by simp)
  exact eU.toLinearEquiv.finrank_eq.symm.trans
    ((AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees.orderedBaseCechHomologyAffineHLinearEquiv π M U hU haU 1).finrank_eq.trans
      ((AlgebraicGeometry.SheafCohomology.Projective.BaseCechAllDegrees.orderedBaseCechHomologyAffineHLinearEquiv π M V hV haV 1).finrank_eq.symm.trans
        eV.toLinearEquiv.finrank_eq))

end

end OAI.RepresentationTheory.Theta.Geometric.CechDimensionComparison
