import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.DerivedEvaluation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.TowerSurjectivity
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SequentialLimit

/-! # Tower Section Lifting -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Framed.TowerSectionLifting.FramedTowerSectionLifting

noncomputable section

/-!
# Global section lifting along the final framed tower

For a native short exact sequence with a Čech-acyclic kernel, evaluation
on every tower level stays exact. Surjective transitions in that kernel
then lift compatible sections through the actual inverse limit, which
computes framed global sections by finality.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Topology.FramedCrystallineTopology.native p k B σ (fun i => r (MvPolynomial.X i))
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ (fun i => r (MvPolynomial.X i))
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Tower.FramedPolynomialTower.tower p k B σ r hr hbase
local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.SheafExactness.FramedCrystallineSheafExactness.restriction p k B σ (fun i => r (MvPolynomial.X i)) V

local instance : HasLimitsOfShape Cᵒᵖ V := ModuleCat.hasLimitsOfShape

def diagram : Sheaf K V ⥤ (ℕᵒᵖ ⥤ V) :=
  sheafToPresheaf K V ⋙ (Functor.whiskeringLeft ℕᵒᵖ Cᵒᵖ V).obj (T).op

def globalIso : Sheaf.Γ K V ≅ diagram p k B σ r hr hbase ⋙ lim :=
  Sheaf.ΓNatIsoLim K V ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf K V) (Functor.Initial.limIso (T).op).symm

def nativeDiagram : Sheaf J V ⥤ (ℕᵒᵖ ⥤ V) := U ⋙ diagram p k B σ r hr hbase

instance nativeDiagram_finiteLimits : PreservesFiniteLimits (nativeDiagram p k B σ r hr hbase) := by
  dsimp [nativeDiagram, diagram]
  infer_instance

def nativeGlobal : Sheaf J V ⥤ V := U ⋙ Sheaf.Γ K V

instance global_additive : (Sheaf.Γ K V).Additive :=
  Functor.additive_of_preserves_binary_products _

instance nativeGlobal_additive : (nativeGlobal p k B σ r).Additive := by
  dsimp [nativeGlobal]
  infer_instance

instance nativeGlobal_finiteLimits : PreservesFiniteLimits (nativeGlobal p k B σ r) := by
  dsimp [nativeGlobal]
  infer_instance

def nativeGlobalIso : nativeGlobal p k B σ r ≅ nativeDiagram p k B σ r hr hbase ⋙ lim :=
  Functor.isoWhiskerLeft U (globalIso p k B σ r hr hbase)

theorem diagram_shortExact (S : ShortComplex (Sheaf J V)) (hS : S.ShortExact)
    (hA : CrystallineCech.CechAcyclic.CrystallineCechAcyclic.Acyclic p k X S.X₁) :
    (S.map (nativeDiagram p k B σ r hr hbase)).ShortExact := by
  have : Mono S.f := hS.mono_f
  have : Mono (S.map (nativeDiagram p k B σ r hr hbase)).f := by
    change Mono ((nativeDiagram p k B σ r hr hbase).map S.f)
    infer_instance
  have : ∀ n, Epi (((nativeDiagram p k B σ r hr hbase).map S.g).app n) := fun n =>
    SectionLifting.CrystallineSectionLifting.epi p k X ((T).obj n.unop).base S hS
      (fun t ht => hA _ t ht 1 (by decide))
  refine { exact := hS.exact.map_of_mono_of_preservesKernel _ inferInstance inferInstance
           mono_f := inferInstance
           epi_g := ?_ }
  change Epi ((nativeDiagram p k B σ r hr hbase).map S.g)
  exact NatTrans.epi_of_epi_app _

theorem global_epi (S : ShortComplex (Sheaf J V)) (hS : S.ShortExact)
    (hA : CrystallineCech.CechAcyclic.CrystallineCechAcyclic.Acyclic p k X S.X₁)
    (ht : ∀ n, Function.Surjective
      (SequentialLimit.SequentialLimitLifting.transition (Site.CoefficientRing p k)
        ((nativeDiagram p k B σ r hr hbase).obj S.X₁) n)) :
    Epi ((nativeGlobal p k B σ r).map S.g) := by
  have : Epi (limMap ((nativeDiagram p k B σ r hr hbase).map S.g)) :=
    SequentialLimit.SequentialLimitLifting.limit_epi _ (S.map (nativeDiagram p k B σ r hr hbase))
      (diagram_shortExact p k B σ r hr hbase S hS hA) ht
  have : Epi ((nativeDiagram p k B σ r hr hbase ⋙ lim).map S.g) := this
  rw [← NatIso.naturality_1 (nativeGlobalIso p k B σ r hr hbase).symm S.g]
  infer_instance

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Framed.TowerSectionLifting.FramedTowerSectionLifting
