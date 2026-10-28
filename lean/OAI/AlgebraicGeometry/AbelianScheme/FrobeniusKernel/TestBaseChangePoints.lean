import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BaseChange

/-! # Test Base Change Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.TestBaseChangePoints.Construction

noncomputable section

/-!
Point-group comparisons for actual base changes and isomorphic test
schemes. Naturality retains both the original test maps and source
scheme maps, so origins, scalar maps and integral actions can all be
transported through the same comparison.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S S' : Scheme.{u}} {g h : ℕ}
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S)

theorem baseChangePoints_precomp {V W : Over S'} (a : V ⟶ W)
    (x : W ⟶ (A.pullback f).scheme) :
    A.baseChangePointsMulEquiv f V (a ≫ x) =
      (Over.map f).map a ≫ A.baseChangePointsMulEquiv f W x := by
  apply Over.OverMorphism.ext
  exact Category.assoc a.left x.left (CategoryTheory.Limits.pullback.fst A.scheme.hom f)

theorem baseChangePoints_postcomp (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S) (p : A.scheme ⟶ B.scheme)
    (V : Over S') (x : V ⟶ (A.pullback f).scheme) :
    B.baseChangePointsMulEquiv f V (x ≫ (Over.pullback f).map p) =
      A.baseChangePointsMulEquiv f V x ≫ p := by
  apply Over.OverMorphism.ext
  change (x.left ≫ ((Over.pullback f).map p).left) ≫
      CategoryTheory.Limits.pullback.fst B.scheme.hom f =
    (x.left ≫ CategoryTheory.Limits.pullback.fst A.scheme.hom f) ≫ p.left
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => x.left ≫ z) (CategoryTheory.Limits.pullback.lift_fst _ _ _)).trans
      (Category.assoc _ _ _).symm)

variable {U : Over S} {V : Over S'} (i : (Over.map f).obj V ≅ U)

def testBaseChangePointsEquiv : (U ⟶ A.scheme) ≃* (V ⟶ (A.pullback f).scheme) :=
  (((yonedaGrp.obj (Grp.mk A.scheme)).mapIso i.op).groupIsoToMulEquiv).trans
    (A.baseChangePointsMulEquiv f V).symm

theorem testBaseChangePointsEquiv_projection (x : U ⟶ A.scheme) :
    A.baseChangePointsMulEquiv f V (testBaseChangePointsEquiv A f i x) = i.hom ≫ x :=
  (A.baseChangePointsMulEquiv f V).apply_symm_apply _

theorem testBaseChangePointsEquiv_postcomp (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S)
    (p : A.scheme ⟶ B.scheme) (x : U ⟶ A.scheme) :
    testBaseChangePointsEquiv B f i (x ≫ p) =
      testBaseChangePointsEquiv A f i x ≫ (Over.pullback f).map p := by
  apply (B.baseChangePointsMulEquiv f V).injective
  exact (testBaseChangePointsEquiv_projection B f i (x ≫ p)).trans
    ((Category.assoc i.hom x p).symm.trans
      ((congrArg (fun z => z ≫ p) (testBaseChangePointsEquiv_projection A f i x).symm).trans
        (baseChangePoints_postcomp A f B p V (testBaseChangePointsEquiv A f i x)).symm))

theorem testBaseChangePointsEquiv_naturality {U' : Over S} {V' : Over S'}
    (i' : (Over.map f).obj V' ≅ U') (a : U ⟶ U') (b : V ⟶ V')
    (hi : (Over.map f).map b ≫ i'.hom = i.hom ≫ a) (x : U' ⟶ A.scheme) :
    testBaseChangePointsEquiv A f i (a ≫ x) =
      b ≫ testBaseChangePointsEquiv A f i' x := by
  apply (A.baseChangePointsMulEquiv f V).injective
  exact (testBaseChangePointsEquiv_projection A f i (a ≫ x)).trans
    ((Category.assoc i.hom a x).symm.trans
      ((congrArg (fun z => z ≫ x) hi.symm).trans
        ((Category.assoc ((Over.map f).map b) i'.hom x).trans
          ((congrArg (fun z => (Over.map f).map b ≫ z)
            (testBaseChangePointsEquiv_projection A f i' x).symm).trans
              (baseChangePoints_precomp A f b (testBaseChangePointsEquiv A f i' x)).symm))))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.TestBaseChangePoints.Construction
