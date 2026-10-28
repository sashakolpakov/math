import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Values
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.PairIndices

/-! # Face Compatibility -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.FaceCompatibility.CrystallineCechFaceCompatibility

noncomputable section

/-!
# Cover-member compatibility supplied by native Čech zero-cocycles

The actual first differential compares the two coface restrictions.
After the singleton-product section identifications, its vanishing gives
compatibility of sections on each pair of original principal opens.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : Site.Object p k X)
  {ι : Type u} (s : ι → Q.thickening.ring)

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "N" => FormalCoproduct.cech (FormalCoproduct.mk ι (OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s))

local instance coefficientSmallLimits : HasLimitsOfSize.{u, u} V :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

def vertex (l : Fin 2) (t : Fin 2 → ι) : Fin 1 → ι :=
  (Cech.ZeroDifferential.CechZeroDifferential.face N l).f t

def factor (l : Fin 2) (t : Fin 2 → ι) :
    CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q (((N).obj (op ⦋1⦌)).obj t) ⟶
      CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q (s (vertex p k X Q s l t 0)) :=
  CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map p k X Q
    ((Cech.ZeroDifferential.CechZeroDifferential.face N l).φ t ≫
      (Values.CrystallineCechValues.singleIso p k X Q s (vertex p k X Q s l t)).hom)

theorem factor_projection (l : Fin 2) (t : Fin 2 → ι) :
    factor p k X Q s l t ≫ CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q
        (s (vertex p k X Q s l t 0)) =
      CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q (((N).obj (op ⦋1⦌)).obj t) :=
  CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map_projection p k X Q _

theorem factor_restriction (F : Sheaf J V) (l : Fin 2) (t : Fin 2 → ι) :
    F.obj.map (factor p k X Q s l t).op =
      (Values.CrystallineCechValues.sectionIso p k X Q s F (vertex p k X Q s l t)).inv ≫
        F.obj.map (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map p k X Q ((Cech.ZeroDifferential.CechZeroDifferential.face N l).φ t)).op := by
  have h := (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.functor p k X Q).map_comp
    ((Cech.ZeroDifferential.CechZeroDifferential.face N l).φ t)
    (Values.CrystallineCechValues.singleIso p k X Q s (vertex p k X Q s l t)).hom
  exact (congrArg (fun f => F.obj.map f.op) h).trans (F.obj.map_comp _ _)

theorem raw_compatible (F : Sheaf J V)
    (z : ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F).X 0)
    (hz : ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F).d 0 1 z = 0)
    (t : Fin 2 → ι) :
    F.obj.map (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map p k X Q ((Cech.ZeroDifferential.CechZeroDifferential.face N 0).φ t)).op
        (Values.CrystallineCechValues.component p k X Q s F z (vertex p k X Q s 0 t)) =
      F.obj.map (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map p k X Q ((Cech.ZeroDifferential.CechZeroDifferential.face N 1).φ t)).op
        (Values.CrystallineCechValues.component p k X Q s F z (vertex p k X Q s 1 t)) := by
  let P := (CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.coefficients p k X Q).obj F
  let π := Pi.π (fun i => P.obj (op (((N).obj (op ⦋1⦌)).obj i))) t
  have hd := congrArg (fun f => f z) (Cech.ZeroDifferential.CechZeroDifferential.differential_component N P t)
  have hzero := (congrArg π hz).trans π.hom.map_zero
  exact sub_eq_zero.mp (hd.symm.trans hzero)

theorem values_compatible (F : Sheaf J V)
    (z : ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F).X 0)
    (hz : ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F).d 0 1 z = 0)
    (t : Fin 2 → ι) :
    F.obj.map (factor p k X Q s 0 t).op
        (Values.CrystallineCechValues.value p k X Q s F z (vertex p k X Q s 0 t)) =
      F.obj.map (factor p k X Q s 1 t).op
        (Values.CrystallineCechValues.value p k X Q s F z (vertex p k X Q s 1 t)) := by
  have h (l : Fin 2) := (congrArg
    (fun f => f (Values.CrystallineCechValues.value p k X Q s F z (vertex p k X Q s l t)))
      (factor_restriction p k X Q s F l t)).trans
        (congrArg (F.obj.map (CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.map p k X Q
          ((Cech.ZeroDifferential.CechZeroDifferential.face N l).φ t)).op)
            (Values.CrystallineCechValues.recover_component p k X Q s F z (vertex p k X Q s l t)))
  exact (h 0).trans ((raw_compatible p k X Q s F z hz t).trans (h 1).symm)

theorem pair_compatible (F : Sheaf J V)
    (z : ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F).X 0)
    (hz : ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F).d 0 1 z = 0)
    (i j : ι) :
    F.obj.map (factor p k X Q s 0 (Cech.PairIndices.CechPairIndices.pair i j)).op
        (Values.CrystallineCechValues.value p k X Q s F z (fun _ => j)) =
      F.obj.map (factor p k X Q s 1 (Cech.PairIndices.CechPairIndices.pair i j)).op
        (Values.CrystallineCechValues.value p k X Q s F z (fun _ => i)) := by
  have h0 := eq_of_heq (Values.CrystallineCechValues.value_congr p k X Q s F z
    (t := vertex p k X Q s 0 (Cech.PairIndices.CechPairIndices.pair i j)) (t' := fun _ => j)
    (Cech.PairIndices.CechPairIndices.zero (CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s) i j))
  have h1 := eq_of_heq (Values.CrystallineCechValues.value_congr p k X Q s F z
    (t := vertex p k X Q s 1 (Cech.PairIndices.CechPairIndices.pair i j)) (t' := fun _ => i)
    (Cech.PairIndices.CechPairIndices.one (CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s) i j))
  exact (congrArg (F.obj.map (factor p k X Q s 0 (Cech.PairIndices.CechPairIndices.pair i j)).op) h0).symm.trans
    ((values_compatible p k X Q s F z hz (Cech.PairIndices.CechPairIndices.pair i j)).trans
      (congrArg (F.obj.map (factor p k X Q s 1 (Cech.PairIndices.CechPairIndices.pair i j)).op) h1))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.FaceCompatibility.CrystallineCechFaceCompatibility
