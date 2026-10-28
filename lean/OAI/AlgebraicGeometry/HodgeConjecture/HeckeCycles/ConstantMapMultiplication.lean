import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantGroupPoints

/-! # Constant Map Multiplication -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantMapMultiplication.CM

noncomputable section

/-! The map constructed from a homomorphism of constant labels preserves
the group operations on every test scheme. The proof restricts to the
open pieces on which the labels are constant. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantGroupPoints.CM

universe u
variable (S : Scheme.{u}) (G : Type u) [Group G]
  (A : Over S) [GrpObj A]

theorem index_one (T : Over S) :
    AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T (1 : T ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X) = LocallyConstant.const T.left 1 :=
  ((AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso S G).hom.app (.op T)).hom.map_one

theorem index_mul (T : Over S) (x y : T ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X) :
    AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T (x * y) = AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T x * AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T y :=
  ((AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso S G).hom.app (.op T)).hom.map_mul x y

theorem preserves_one (p : G →* (Over.mk (𝟙 S) ⟶ A)) (T : Over S) :
    (1 : T ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X) ≫ ConstantGroupPoints.CM.schemeMap S G A p = 1 := by
  let b : T ⟶ Over.mk (𝟙 S) := Over.homMk T.hom (Category.comp_id T.hom)
  have h := ConstantPointMap.CM.ofPoints_on_constant S G A p T
    (1 : T ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X) 1
    (fun t => congrArg (fun c : LocallyConstant T.left G => c t) (index_one S G T))
  exact h.trans ((congrArg (fun z => b ≫ z) p.map_one).trans (MonObj.comp_one b))

theorem preserves_mul (p : G →* (Over.mk (𝟙 S) ⟶ A)) (T : Over S)
    (x y : T ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X) :
    (x * y) ≫ ConstantGroupPoints.CM.schemeMap S G A p =
      (x ≫ ConstantGroupPoints.CM.schemeMap S G A p) * (y ≫ ConstantGroupPoints.CM.schemeMap S G A p) := by
  let c : LocallyConstant T.left (G × G) := {
    toFun t := (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T x t, AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T y t)
    isLocallyConstant := (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T x).isLocallyConstant.prodMk
      (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T y).isLocallyConstant }
  let U (i : G × G) : Over S := Over.mk ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c i).ι ≫ T.hom)
  let d (i : G × G) : U i ⟶ T := Over.homMk (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c i).ι rfl
  have hlocal (i : G × G) :
      d i ≫ ((x * y) ≫ ConstantGroupPoints.CM.schemeMap S G A p) =
        d i ≫ ((x ≫ ConstantGroupPoints.CM.schemeMap S G A p) * (y ≫ ConstantGroupPoints.CM.schemeMap S G A p)) := by
    have hxi (t : (U i).left) : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint (U i) (d i ≫ x) t = i.1 :=
      congrArg Prod.fst t.property
    have hyi (t : (U i).left) : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint (U i) (d i ≫ y) t = i.2 :=
      congrArg Prod.snd t.property
    have hxyi (t : (U i).left) :
        AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint (U i) ((d i ≫ x) * (d i ≫ y)) t = i.1 * i.2 :=
      (congrArg (fun c : LocallyConstant (U i).left G => c t)
        (index_mul S G (U i) (d i ≫ x) (d i ≫ y))).trans
          (congrArg₂ (· * ·) (hxi t) (hyi t))
    let b : U i ⟶ Over.mk (𝟙 S) := Over.homMk (U i).hom (Category.comp_id (U i).hom)
    have hx := ConstantPointMap.CM.ofPoints_on_constant S G A p (U i) (d i ≫ x) i.1 hxi
    have hy := ConstantPointMap.CM.ofPoints_on_constant S G A p (U i) (d i ≫ y) i.2 hyi
    have hxy := ConstantPointMap.CM.ofPoints_on_constant S G A p (U i)
      ((d i ≫ x) * (d i ≫ y)) (i.1 * i.2) hxyi
    calc
      d i ≫ ((x * y) ≫ ConstantGroupPoints.CM.schemeMap S G A p) =
          ((d i ≫ x) * (d i ≫ y)) ≫ ConstantGroupPoints.CM.schemeMap S G A p := by
        rw [← Category.assoc, MonObj.comp_mul]
      _ = b ≫ p (i.1 * i.2) := hxy
      _ = b ≫ (p i.1 * p i.2) := congrArg (fun z => b ≫ z) (p.map_mul i.1 i.2)
      _ = (b ≫ p i.1) * (b ≫ p i.2) := MonObj.comp_mul b (p i.1) (p i.2)
      _ = ((d i ≫ x) ≫ ConstantGroupPoints.CM.schemeMap S G A p) * ((d i ≫ y) ≫ ConstantGroupPoints.CM.schemeMap S G A p) :=
        congrArg₂ (· * ·) hx.symm hy.symm
      _ = d i ≫ ((x ≫ ConstantGroupPoints.CM.schemeMap S G A p) * (y ≫ ConstantGroupPoints.CM.schemeMap S G A p)) := by
        rw [MonObj.comp_mul, Category.assoc, Category.assoc]
  apply Over.OverMorphism.ext
  apply (cancel_epi (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFibersIso c).hom).mp
  apply Sigma.hom_ext
  intro i
  rw [AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFibersIso_ι_hom_assoc, AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFibersIso_ι_hom_assoc]
  exact congrArg (fun z : U i ⟶ A => z.left) (hlocal i)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantMapMultiplication.CM
