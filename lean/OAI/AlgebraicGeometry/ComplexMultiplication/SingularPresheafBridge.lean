import OAI.AlgebraicGeometry.ComplexMultiplication.SingularCochainBridge
import OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf
import OAI.AlgebraicTopology.Singular.SheafCochain

/-! # Singular Presheaf Bridge -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SingularPresheafBridge

noncomputable section

/-! # Evaluation identifies the actual singular presheaf complexes

Both constructions use the same continuous simplices on every open subspace.
The comparison is actual evaluation on chains and retains restriction and the
singular coboundary, after literal forgetting of module scalars.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable (R : Type) [CommRing R] (Y : TopCat.{0})

/-- Evaluation on actual chains in every degree and on every open subspace. -/
def singularCochainDegreePresheafBridgeIso (n : ℕ) :
    AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf (ModuleCat.of R R) Y n ⋙
        forget₂ (ModuleCat R) AddCommGrpCat ≅
      AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf R Y n :=
  NatIso.ofComponents
    (fun U => (forget₂ (ModuleCat R) AddCommGrpCat).mapIso
      ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n).mapIso
        (SingularCochainBridge.singularCochainBridgeIso R (TopCat.of U.unop))))
    (fun {U V} i => by
      apply ConcreteCategory.hom_ext
      intro φ
      exact ConcreteCategory.congr_hom
        (congrArg (fun f => (forget₂ (ModuleCat R) AddCommGrpCat).map (f.f n))
          (SingularCochainBridge.singularCochainBridgeIso_naturality R ((Opens.toTopCat Y).map i.unop))) φ)

/-- The actual local component of the degreewise evaluation comparison. -/
theorem singularCochainDegreePresheafBridgeIso_hom_app (U : (Opens Y)ᵒᵖ) (n : ℕ) :
    (singularCochainDegreePresheafBridgeIso R Y n).hom.app U =
      (forget₂ (ModuleCat R) AddCommGrpCat).map
        ((SingularCochainBridge.singularCochainBridgeIso R (TopCat.of U.unop)).hom.f n) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluation retains the actual adjacent-degree coboundary on every open. -/
theorem singularCochainDegreePresheafBridgeIso_coboundary (n : ℕ) :
    (singularCochainDegreePresheafBridgeIso R Y n).hom ≫
        AlgebraicTopology.Singular.SheafCochain.singularCochainCoboundary R Y n =
      Functor.whiskerRight
        ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of R R) Y).d n (n + 1))
        (forget₂ (ModuleCat R) AddCommGrpCat) ≫
          (singularCochainDegreePresheafBridgeIso R Y (n + 1)).hom := by
  apply NatTrans.ext
  funext U
  change (singularCochainDegreePresheafBridgeIso R Y n).hom.app U ≫
      (AlgebraicTopology.Singular.SheafCochain.singularCochainCoboundary R Y n).app U =
    (forget₂ (ModuleCat R) AddCommGrpCat).map
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) (TopCat.of U.unop)).d
        n (n + 1)) ≫ (singularCochainDegreePresheafBridgeIso R Y (n + 1)).hom.app U
  rw [singularCochainDegreePresheafBridgeIso_hom_app,
    singularCochainDegreePresheafBridgeIso_hom_app]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  apply LinearMap.ext
  intro c
  change (AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv
      (TopCat.toSSet.obj (TopCat.of U.unop)) (ModuleCat.of R R) n φ)
        (((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) (TopCat.of U.unop)).d
          (n + 1) n).hom c) =
    (AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv
      (TopCat.toSSet.obj (TopCat.of U.unop)) (ModuleCat.of R R) (n + 1)
        ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) (TopCat.of U.unop)).d
          n (n + 1) φ)) c
  exact LinearMap.congr_fun
    (AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_d
      (TopCat.toSSet.obj (TopCat.of U.unop)) (ModuleCat.of R R) n (n + 1) φ).symm c

set_option backward.isDefEq.respectTransparency false in
/-- The actual evaluation comparison also retains every singular coboundary. -/
def singularPresheafComplexBridgeIso :
    (Functor.mapHomologicalComplex
      ((Functor.whiskeringRight (Opens Y)ᵒᵖ (ModuleCat R) AddCommGrpCat).obj
        (forget₂ (ModuleCat R) AddCommGrpCat)) (ComplexShape.up ℕ)).obj
          (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of R R) Y) ≅
      AlgebraicTopology.Singular.SheafCochain.singularCochainPresheafComplex R Y :=
  HomologicalComplex.Hom.isoOfComponents
    (singularCochainDegreePresheafBridgeIso R Y)
    (fun i j hij => by
      obtain rfl := hij
      rw [Functor.mapHomologicalComplex_obj_d,
        AlgebraicTopology.Singular.SheafCochain.singularCochainPresheafComplex_d]
      exact singularCochainDegreePresheafBridgeIso_coboundary R Y i)

/-- On actual local cochains, the comparison is exactly the proved chain evaluation. -/
theorem singularPresheafComplexBridgeIso_hom_f_app (U : Opens Y) (n : ℕ) :
    ((singularPresheafComplexBridgeIso R Y).hom.f n).app (op U) =
      (forget₂ (ModuleCat R) AddCommGrpCat).map
        ((SingularCochainBridge.singularCochainBridgeIso R (TopCat.of U)).hom.f n) := rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SingularPresheafBridge
