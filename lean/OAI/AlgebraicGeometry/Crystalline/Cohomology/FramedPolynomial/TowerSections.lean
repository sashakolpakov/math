import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Tower
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.DerivedSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.WittFrames
import Mathlib.CategoryTheory.Sites.GlobalSections

/-! # Tower Sections -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.TowerSections

noncomputable section

/-!
# Global sections as the limit of the actual framed polynomial tower

Finality identifies framed global sections with the countable inverse
system of sections on the actual p-power envelope levels. The constructed
finite Witt presentation specializes this result to every finite-type
residue algebra, with no additional presentation supplied.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Limits

namespace FramedPolynomialTowerSections

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafPushforward.CrystallineFrameSheafPushforward.Coefficients p k
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ (fun i => r (MvPolynomial.X i))
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Topology.FramedCrystallineTopology.native p k B σ (fun i => r (MvPolynomial.X i))
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Tower.FramedPolynomialTower.tower p k B σ r hr hbase

local instance presheafLimits : HasLimitsOfShape Cᵒᵖ V := ModuleCat.hasLimitsOfShape

def presheafLimitIso (P : Cᵒᵖ ⥤ V) : limit P ≅ limit ((T).op ⋙ P) :=
  (Functor.Initial.limitIso (T).op P).symm

def globalSectionsIso (S : Sheaf K V) : (Sheaf.Γ K V).obj S ≅ limit ((T).op ⋙ S.obj) :=
  (Sheaf.ΓNatIsoLim K V).app S ≪≫ presheafLimitIso p k B σ r hr hbase S.obj

end FramedPolynomialTowerSections

namespace FiniteFramedPolynomialTower

universe u

variable (p : ℕ) [Fact p.Prime] (k B : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] [Algebra.FiniteType k B]

def coordinates : Finite.WittFrames.FiniteWittFrames.Variables k B → B :=
  fun i => Finite.WittFrames.FiniteWittFrames.reduction k B p (MvPolynomial.X i)

def tower : ℕ ⥤ FramedCrystalline.Category.FramedCrystallineCategory.Object p k B (Finite.WittFrames.FiniteWittFrames.Variables k B) (coordinates p k B) :=
  Tower.FramedPolynomialTower.tower p k B (Finite.WittFrames.FiniteWittFrames.Variables k B) (Finite.WittFrames.FiniteWittFrames.reduction k B p)
    (Finite.WittFrames.FiniteWittFrames.reduction_surjective k B p) (Finite.WittFrames.FiniteWittFrames.reduction_base k B p)

instance final : (tower p k B).Final :=
  Tower.FramedPolynomialTower.final p k B (Finite.WittFrames.FiniteWittFrames.Variables k B) (Finite.WittFrames.FiniteWittFrames.reduction k B p)
    (Finite.WittFrames.FiniteWittFrames.reduction_surjective k B p) (Finite.WittFrames.FiniteWittFrames.reduction_base k B p)

local instance presheafLimits : HasLimitsOfShape
    (FramedCrystalline.Category.FramedCrystallineCategory.Object p k B (Finite.WittFrames.FiniteWittFrames.Variables k B) (coordinates p k B))ᵒᵖ
    (CrystallineFrame.SheafPushforward.CrystallineFrameSheafPushforward.Coefficients p k) := ModuleCat.hasLimitsOfShape

def globalSectionsIso
    (S : Sheaf (FramedCrystalline.Topology.FramedCrystallineTopology.native p k B (Finite.WittFrames.FiniteWittFrames.Variables k B) (coordinates p k B))
      (CrystallineFrame.SheafPushforward.CrystallineFrameSheafPushforward.Coefficients p k)) :
    (Sheaf.Γ _ _).obj S ≅ limit ((tower p k B).op ⋙ S.obj) :=
  FramedPolynomialTowerSections.globalSectionsIso p k B (Finite.WittFrames.FiniteWittFrames.Variables k B) (Finite.WittFrames.FiniteWittFrames.reduction k B p)
    (Finite.WittFrames.FiniteWittFrames.reduction_surjective k B p) (Finite.WittFrames.FiniteWittFrames.reduction_base k B p) S

end FiniteFramedPolynomialTower

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.TowerSections
