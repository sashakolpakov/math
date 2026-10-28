import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.FaceCompatibility
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.ProductLift

/-! # Overlaps -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Overlaps.CrystallineCechOverlaps

noncomputable section

/-!
# Native overlap compatibility of principal Čech zero-cocycles

An arbitrary native overlap maps to the actual pair intersection in the
Čech nerve. Its two projections recover the given overlap maps because
principal projections are monomorphisms. Consequently the pair equations
of a zero-cocycle give the compatibility required by the native sheaf axiom.
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

variable (i j : ι) (T : Site.Object p k X)
  (f : T ⟶ CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q (s i))
  (g : T ⟶ CrystallinePrincipal.Opens.CrystallinePrincipalOpens.object p k X Q (s j))
  (h : f ≫ CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q (s i) =
    g ≫ CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q (s j))

def pairCone (l : Fin 2) :
    Over.mk (f ≫ CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q (s i)) ⟶
      (CrystallinePrincipal.Slice.CrystallinePrincipalSlice.functor p k X Q).obj
        (CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s (Cech.PairIndices.CechPairIndices.pair i j l)) :=
  Fin.cases (Over.homMk f rfl) (fun _ => Over.homMk g h.symm) l

def lift : T ⟶ CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.object p k X Q
    (((N).obj (op ⦋1⦌)).obj (Cech.PairIndices.CechPairIndices.pair i j)) :=
  (CrystallinePrincipal.ProductLift.CrystallinePrincipalProductLift.lift p k X Q
    (fun l : Fin 2 => CrystallinePrincipal.Cech.CrystallinePrincipalCech.family s (Cech.PairIndices.CechPairIndices.pair i j l))
    (Over.mk (f ≫ CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q (s i)))
    (pairCone p k X Q s i j T f g h)).left

theorem lift_over :
    lift p k X Q s i j T f g h ≫ CrystallinePrincipal.Functor.CrystallinePrincipalFunctor.projection p k X Q
      (((N).obj (op ⦋1⦌)).obj (Cech.PairIndices.CechPairIndices.pair i j)) =
        f ≫ CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q (s i) :=
  Over.w _

theorem lift_factor_zero :
    lift p k X Q s i j T f g h ≫
      FaceCompatibility.CrystallineCechFaceCompatibility.factor p k X Q s 0 (Cech.PairIndices.CechPairIndices.pair i j) = g := by
  apply (cancel_mono (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q (s j))).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => lift p k X Q s i j T f g h ≫ a)
      (FaceCompatibility.CrystallineCechFaceCompatibility.factor_projection p k X Q s 0
        (Cech.PairIndices.CechPairIndices.pair i j))).trans ((lift_over p k X Q s i j T f g h).trans h))

theorem lift_factor_one :
    lift p k X Q s i j T f g h ≫
      FaceCompatibility.CrystallineCechFaceCompatibility.factor p k X Q s 1 (Cech.PairIndices.CechPairIndices.pair i j) = f := by
  apply (cancel_mono (CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q (s i))).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => lift p k X Q s i j T f g h ≫ a)
      (FaceCompatibility.CrystallineCechFaceCompatibility.factor_projection p k X Q s 1
        (Cech.PairIndices.CechPairIndices.pair i j))).trans (lift_over p k X Q s i j T f g h))

include h in
theorem compatible (F : Sheaf J V)
    (z : ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F).X 0)
    (hz : ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q s).obj F).d 0 1 z = 0) :
    F.obj.map f.op (Values.CrystallineCechValues.value p k X Q s F z (fun _ => i)) =
      F.obj.map g.op (Values.CrystallineCechValues.value p k X Q s F z (fun _ => j)) := by
  have hc := congrArg (F.obj.map (lift p k X Q s i j T f g h).op)
    (FaceCompatibility.CrystallineCechFaceCompatibility.pair_compatible p k X Q s F z hz i j)
  have h0 := (F.obj.map_comp
    (FaceCompatibility.CrystallineCechFaceCompatibility.factor p k X Q s 0 (Cech.PairIndices.CechPairIndices.pair i j)).op
    (lift p k X Q s i j T f g h).op).symm.trans
      (congrArg (fun a => F.obj.map a.op) (lift_factor_zero p k X Q s i j T f g h))
  have h1 := (F.obj.map_comp
    (FaceCompatibility.CrystallineCechFaceCompatibility.factor p k X Q s 1 (Cech.PairIndices.CechPairIndices.pair i j)).op
    (lift p k X Q s i j T f g h).op).symm.trans
      (congrArg (fun a => F.obj.map a.op) (lift_factor_one p k X Q s i j T f g h))
  exact (congrArg (fun a => a (Values.CrystallineCechValues.value p k X Q s F z (fun _ => i))) h1).symm.trans
    (hc.symm.trans
      (congrArg (fun a => a (Values.CrystallineCechValues.value p k X Q s F z (fun _ => j))) h0))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.Overlaps.CrystallineCechOverlaps
