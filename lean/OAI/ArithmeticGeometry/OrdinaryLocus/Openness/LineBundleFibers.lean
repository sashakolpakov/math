import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleQuasicoherent
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Line Bundle Fibers -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleFibers.Construction

noncomputable section

/-! Trivializations and bases of line bundles over scheme points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- A line bundle on a nonempty one-point scheme is globally trivial. -/
def lineBundleTrivializationOfSubsingleton
    {X : Scheme.{u}} [Nonempty X] [Subsingleton X]
    (M : X.Modules) (hM : LineBundle.Construction.IsLineBundle M) : M ≅ LineBundle.Construction.structureSheafModule X := by
  let x : X := Classical.choice inferInstance
  let U := (hM x).choose
  have hx : x ∈ U := (hM x).choose_spec.1
  have he : Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ LineBundle.Construction.structureSheafModule U.toScheme) :=
    (hM x).choose_spec.2
  have hU : U = ⊤ := by
    apply le_antisymm le_top
    intro y _
    rwa [Subsingleton.elim y x]
  have htop : Nonempty ((Scheme.Modules.pullback (⊤ : X.Opens).ι).obj M ≅
      LineBundle.Construction.structureSheafModule (⊤ : X.Opens).toScheme) := hU ▸ he
  let e := Classical.choice htop
  exact ((Scheme.Modules.pullbackId X).app M).symm ≪≫
    (Scheme.Modules.pullbackCongr X.toIso_inv_ι.symm).app M ≪≫
    ((Scheme.Modules.pullbackComp X.topIso.inv (⊤ : X.Opens).ι).app M).symm ≪≫
    (Scheme.Modules.pullback X.topIso.inv).mapIso e ≪≫
    LineBundle.Construction.pullbackStructureSheafIso X.topIso.inv

/-- Every field-valued fiber of a line bundle is a trivial line bundle. -/
def lineBundleFiberTrivialization
    {k : Type u} [Field k] {X : Scheme.{u}}
    (x : Spec (.of k) ⟶ X) (M : X.Modules) (hM : LineBundle.Construction.IsLineBundle M) :
    (Scheme.Modules.pullback x).obj M ≅ LineBundle.Construction.structureSheafModule (Spec (.of k)) :=
  lineBundleTrivializationOfSubsingleton _ (LineBundle.Construction.isLineBundle_pullback x M hM)

/-- The vector space of sections of the fiber over a field-valued point. -/
def lineBundleFiberModule
    {k : Type u} [Field k] {X : Scheme.{u}}
    (x : Spec (.of k) ⟶ X) (M : X.Modules) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv).hom).obj
    ((SheafOfModules.evaluation (Spec (.of k)).ringCatSheaf (.op ⊤)).obj
      ((Scheme.Modules.pullback x).obj M))

def structureSheafFieldSectionsIso (k : Type u) [Field k] :
    (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv).hom).obj
      ((SheafOfModules.evaluation (Spec (.of k)).ringCatSheaf (.op ⊤)).obj
        (LineBundle.Construction.structureSheafModule (Spec (.of k)))) ≅
        ModuleCat.of k k := by
  refine ModuleCat.isoMk
    ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapIso
      (Scheme.ΓSpecIso (.of k))) ?_
  intro r
  ext a
  let a' : Γ(Spec (.of k), ⊤) := a
  change r * (Scheme.ΓSpecIso (.of k)).hom a' =
    (Scheme.ΓSpecIso (.of k)).hom ((Scheme.ΓSpecIso (.of k)).inv r * a')
  simp

def lineBundleFiberModuleIso
    {k : Type u} [Field k] {X : Scheme.{u}}
    (x : Spec (.of k) ⟶ X) (M : X.Modules) (hM : LineBundle.Construction.IsLineBundle M) :
    lineBundleFiberModule x M ≅ ModuleCat.of k k :=
  (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv).hom).mapIso
    ((SheafOfModules.evaluation (Spec (.of k)).ringCatSheaf (.op ⊤)).mapIso
      (lineBundleFiberTrivialization x M hM)) ≪≫
    structureSheafFieldSectionsIso k

def lineBundleFiberBasis
    {k : Type u} [Field k] {X : Scheme.{u}}
    (x : Spec (.of k) ⟶ X) (M : X.Modules) (hM : LineBundle.Construction.IsLineBundle M) :
    Module.Basis PUnit.{u+1} k (lineBundleFiberModule x M) :=
  (Module.Basis.singleton PUnit.{u+1} k).map (lineBundleFiberModuleIso x M hM).symm.toLinearEquiv

theorem finrank_lineBundleFiberModule
    {k : Type u} [Field k] {X : Scheme.{u}}
    (x : Spec (.of k) ⟶ X) (M : X.Modules) (hM : LineBundle.Construction.IsLineBundle M) :
    Module.finrank k (lineBundleFiberModule x M) = 1 := by
  rw [Module.finrank_eq_card_basis (lineBundleFiberBasis x M hM)]
  simp

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleFibers.Construction
