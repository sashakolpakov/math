import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterLevelPointComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismBaseChange

/-! # Geometric Transport Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Equality of geometric torsion maps after parameter base change forces
the actual ordered full levels to agree after the canonical family iso. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {g N : ℕ} {U T : Over S}
variable (A : Abelian.Schemes.AbelianScheme g S) (c : U ⟶ T)
variable (lT : (A.pullback T.hom).FullLevel N) (lU : (A.pullback U.hom).FullLevel N)

theorem Abelian.Schemes.AbelianScheme.FullLevel.transport_parameterPullback_of_geometric
    (h : (Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv A N U.hom lU).hom.hom.hom =
      Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c (Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv A N T.hom lT).hom.hom.hom) :
    (lT.pullback c.left).transport (A.parameterPullbackIso c).symm = lU := by
  let C := Level.Scheme.constantFullLevelScheme g N S
  let φT := (Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv A N T.hom lT).hom.hom.hom
  let φU := (Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv A N U.hom lU).hom.hom.hom
  have hφ : φU.left ≫ pullback.fst (A.torsionScheme N).hom U.hom =
      Single.ParameterBaseChange.singleParameterBaseChangeMap c C ≫ φT.left ≫ pullback.fst (A.torsionScheme N).hom T.hom := by
    calc
      φU.left ≫ pullback.fst (A.torsionScheme N).hom U.hom =
          φU.left ≫ (Single.ParameterBaseChange.singleParameterBaseChangeMap c (A.torsionScheme N) ≫
            pullback.fst (A.torsionScheme N).hom T.hom) :=
        congrArg (fun k => φU.left ≫ k) (Single.ParameterBaseChange.singleParameterBaseChangeMap_comp c (A.torsionScheme N)).symm
      _ = (Single.ParameterBaseChange.singleParameterBaseChangeMap c C ≫ φT.left) ≫
          pullback.fst (A.torsionScheme N).hom T.hom := by
        rw [← Category.assoc, show φU = Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c φT from h,
          Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange_comp]
      _ = _ := Category.assoc _ _ _
  apply Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro V labels
  let q : V ⟶ (Over.pullback U.hom).obj C :=
    (Level.LevelPullbackGeometry.constantFullLevelBaseChangeYonedaIso g N U.hom).inv.app (.op V) labels
  have hq : (Level.LevelPullbackGeometry.constantFullLevelBaseChangeYonedaIso g N U.hom).hom.app (.op V) q = labels :=
    ConcreteCategory.congr_hom (CC := fun X : GrpCat.{u} => X)
      ((Level.LevelPullbackGeometry.constantFullLevelBaseChangeYonedaIso g N U.hom).app (.op V)).inv_hom_id labels
  let qT := ParameterLevelPointComparison.parameterPointToLargerBase c C V q
  have hqT : (Level.LevelPullbackGeometry.constantFullLevelBaseChangeYonedaIso g N T.hom).hom.app
      (.op ((Over.map c.left).obj V)) qT = labels :=
    (ParameterLevelPointComparison.constantLevelLabels_parameterPoint c g N V q).trans hq
  let x := ((lT.pullback c.left).hom.app (.op V) labels).val
  let y := (lT.hom.app (.op ((Over.map c.left).obj V)) labels).val
  let z := (lU.hom.app (.op V) labels).val
  have hx : x.left ≫ pullback.fst (A.pullback T.hom).scheme.hom c.left = y.left :=
    congrArg (fun a : (A.pullback T.hom).Points ((Over.map c.left).obj V) => a.left)
      (lT.pullback_basis c.left V labels)
  have hT := Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv_original_point A N T.hom lT
    ((Over.map c.left).obj V) qT
  rw [hqT] at hT
  have hU := Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv_original_point A N U.hom lU V q
  rw [hq] at hU
  apply (A.baseChangePointsEquiv U.hom V).injective
  apply Over.OverMorphism.ext
  change (x.left ≫ (A.parameterPullbackIso c).inv.left) ≫ pullback.fst A.scheme.hom U.hom =
    z.left ≫ pullback.fst A.scheme.hom U.hom
  calc
    (x.left ≫ (A.parameterPullbackIso c).inv.left) ≫ pullback.fst A.scheme.hom U.hom =
        x.left ≫ pullback.fst (A.pullback T.hom).scheme.hom c.left ≫
          pullback.fst A.scheme.hom T.hom := by
      exact (Category.assoc _ _ _).trans
        (congrArg (fun f => x.left ≫ f)
          (ParameterLevelPointComparison.singleParameterBaseChangeIso_inv_original_fst c A.scheme))
    _ = y.left ≫ pullback.fst A.scheme.hom T.hom := by
      erw [← Category.assoc, hx]
    _ = qT.left ≫ φT.left ≫ pullback.fst (A.torsionScheme N).hom T.hom ≫
        (A.torsionInclusion N).left := hT.symm
    _ = q.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap c C ≫ φT.left ≫
        pullback.fst (A.torsionScheme N).hom T.hom ≫ (A.torsionInclusion N).left := by
      change (q.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap c C) ≫ φT.left ≫
        pullback.fst (A.torsionScheme N).hom T.hom ≫ (A.torsionInclusion N).left = _
      rw [Category.assoc]
    _ = q.left ≫ φU.left ≫ pullback.fst (A.torsionScheme N).hom U.hom ≫
        (A.torsionInclusion N).left := by
      simpa only [Category.assoc] using congrArg
        (fun k => q.left ≫ k ≫ (A.torsionInclusion N).left) hφ.symm
    _ = z.left ≫ pullback.fst A.scheme.hom U.hom := hU

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
