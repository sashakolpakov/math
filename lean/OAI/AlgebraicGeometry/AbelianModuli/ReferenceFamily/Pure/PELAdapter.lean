import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseChange

/-! # PEL Adapter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.PELAdapter

noncomputable section

/-! The pure polarized problem embeds in the implemented family category
by the canonical integer action. This permits use of proved field descent
without imposing any additional endomorphism structure on a pure family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli

variable {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}

def endSchemeAddMap (A : Over S) [GrpObj A] [IsCommMonObj A] :
    AbelianScheme.TateComparison.End.IntegralEnd A →+ Additive (A ⟶ A) where
  toFun f := Additive.ofMul (AbelianScheme.TateComparison.End.endSchemeMap A f)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem endSchemeMap_intCast (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℤ) :
    AbelianScheme.TateComparison.End.endSchemeMap A (n : AbelianScheme.TateComparison.End.IntegralEnd A) = (𝟙 A) ^ n := by
  have h : endSchemeAddMap A (n : AbelianScheme.TateComparison.End.IntegralEnd A) = n • endSchemeAddMap A 1 := by
    simpa only [zsmul_one] using (endSchemeAddMap A).map_zsmul n (1 : AbelianScheme.TateComparison.End.IntegralEnd A)
  exact congrArg Additive.toMul h

def pureAsPEL (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) :
    AbelianScheme.TateComparison.PEL.PELFamilyData ℤ g N S :=
  AbelianScheme.TateComparison.PEL.PELFamilyData.ofPolarized A (Int.castRingHom (AbelianScheme.TateComparison.End.IntegralEnd A.abelian.scheme))

def pureIsoAsPEL {A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S}
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B) : AbelianScheme.TateComparison.PELModuli.PELFamilyIso (pureAsPEL A) (pureAsPEL B) where
  abelian := e.abelian
  dual := e.dual
  abelianGroup := e.abelianGroup
  dualGroup := e.dualGroup
  polarization := e.polarization
  poincare := e.poincare
  equivariant n := by
    change AbelianScheme.TateComparison.End.endSchemeMap A.abelian.scheme (n : AbelianScheme.TateComparison.End.IntegralEnd A.abelian.scheme) ≫ e.abelian.hom =
      e.abelian.hom ≫ AbelianScheme.TateComparison.End.endSchemeMap B.abelian.scheme (n : AbelianScheme.TateComparison.End.IntegralEnd B.abelian.scheme)
    rw [endSchemeMap_intCast, endSchemeMap_intCast, GrpObj.zpow_comp,
      GrpObj.comp_zpow, Category.id_comp, Category.comp_id]
  marking := e.level

def pureIsoOfPEL {A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S}
    (e : AbelianScheme.TateComparison.PELModuli.PELFamilyIso (pureAsPEL A) (pureAsPEL B)) : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B where
  abelian := e.abelian
  dual := e.dual
  abelianGroup := e.abelianGroup
  dualGroup := e.dualGroup
  polarization := e.polarization
  poincare := e.poincare
  level := e.marking

def pureIsoAsPELWithActions {A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S}
    (a : ℤ →+* AbelianScheme.TateComparison.End.IntegralEnd A.abelian.scheme) (b : ℤ →+* AbelianScheme.TateComparison.End.IntegralEnd B.abelian.scheme)
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B) :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso (AbelianScheme.TateComparison.PEL.PELFamilyData.ofPolarized A a) (AbelianScheme.TateComparison.PEL.PELFamilyData.ofPolarized B b) where
  abelian := e.abelian
  dual := e.dual
  abelianGroup := e.abelianGroup
  dualGroup := e.dualGroup
  polarization := e.polarization
  poincare := e.poincare
  equivariant n := by
    have ha : a n = (n : AbelianScheme.TateComparison.End.IntegralEnd A.abelian.scheme) := map_intCast a n
    have hb : b n = (n : AbelianScheme.TateComparison.End.IntegralEnd B.abelian.scheme) := map_intCast b n
    change AbelianScheme.TateComparison.End.endSchemeMap A.abelian.scheme (a n) ≫ e.abelian.hom =
      e.abelian.hom ≫ AbelianScheme.TateComparison.End.endSchemeMap B.abelian.scheme (b n)
    rw [ha, hb, endSchemeMap_intCast, endSchemeMap_intCast, GrpObj.zpow_comp,
      GrpObj.comp_zpow, Category.id_comp, Category.comp_id]
  marking := e.level

def pureIsoOfPELWithActions {A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S}
    {a : ℤ →+* AbelianScheme.TateComparison.End.IntegralEnd A.abelian.scheme} {b : ℤ →+* AbelianScheme.TateComparison.End.IntegralEnd B.abelian.scheme}
    (e : AbelianScheme.TateComparison.PELModuli.PELFamilyIso (AbelianScheme.TateComparison.PEL.PELFamilyData.ofPolarized A a) (AbelianScheme.TateComparison.PEL.PELFamilyData.ofPolarized B b)) :
    HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B where
  abelian := e.abelian
  dual := e.dual
  abelianGroup := e.abelianGroup
  dualGroup := e.dualGroup
  polarization := e.polarization
  poincare := e.poincare
  level := e.marking

def purePullbackIsoAsPEL (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    {T : Scheme.{0}} (b : T ⟶ S)
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback b) (A.pullback b)) :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso ((pureAsPEL A).pullback b) ((pureAsPEL A).pullback b) :=
  pureIsoAsPELWithActions _ _ e

def purePullbackIsoOfPEL (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    {T : Scheme.{0}} (b : T ⟶ S)
    (e : AbelianScheme.TateComparison.PELModuli.PELFamilyIso ((pureAsPEL A).pullback b) ((pureAsPEL A).pullback b)) :
    HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback b) (A.pullback b) :=
  pureIsoOfPELWithActions e

theorem pureAsPEL_pullback (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    {T : Scheme.{0}} (b : T ⟶ S) :
    (pureAsPEL A).pullback b = pureAsPEL (A.pullback b) := by
  have h : (AbelianScheme.TateComparison.BaseChange.endBaseChange A.abelian.scheme b).comp
      (Int.castRingHom (AbelianScheme.TateComparison.End.IntegralEnd A.abelian.scheme)) =
      Int.castRingHom (AbelianScheme.TateComparison.End.IntegralEnd (A.abelian.pullback b).scheme) :=
    Subsingleton.elim _ _
  exact congrArg (fun action => AbelianScheme.TateComparison.PEL.PELFamilyData.ofPolarized (A.pullback b) action) h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.PELAdapter
