import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.DerivedAdjunction

/-! # Derived Sections -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.DerivedSections.FramedCrystallineDerivedSections

noncomputable section

/-!
# Derived global sections through the actual framed crystalline site

The native rank-one coefficient sheaf restricts to the rank-one coefficient
sheaf on the framed site. The proved derived adjunction consequently
identifies derived global sections of every framed complex with those
of its exact native frame pushforward.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Topology.FramedCrystallineTopology.native p k B σ a
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafPushforward.CrystallineFrameSheafPushforward.Coefficients p k
local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.ExactAdjunction.FramedCrystallineExactAdjunction.restriction p k B σ a
local notation "G" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.ExactAdjunction.FramedCrystallineExactAdjunction.frame p k B σ a
local notation "NS" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.DerivedAdjunction.FramedCrystallineDerivedAdjunction.NativeSheaves p k B
local notation "FS" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.DerivedAdjunction.FramedCrystallineDerivedAdjunction.FramedSheaves p k B σ a

local instance nativeDerived : HasDerivedCategory.{u + 2} NS := HasDerivedCategory.standard _
local instance framedDerived : HasDerivedCategory.{u + 2} FS := HasDerivedCategory.standard _

def coefficientSheaf : FS := (constantSheaf K V).obj
  (ModuleCat.of (Site.CoefficientRing p k) (Site.CoefficientRing p k))

def coefficientIso : (U).obj (Site.coefficientSheaf p k X) ≅ coefficientSheaf p k B σ a :=
  (((Category.FramedCrystallineCategory.forget p k B σ a).pushforwardContinuousSheafificationCompatibility V K J).app
    ((Functor.const (Site.Object p k X)ᵒᵖ).obj
      (ModuleCat.of (Site.CoefficientRing p k) (Site.CoefficientRing p k)))).symm

def nativeCoefficientComplex : CochainComplex NS ℤ :=
  (HomologicalComplex.single NS (ComplexShape.up ℤ) 0).obj (Site.coefficientSheaf p k X)

def framedCoefficientComplex : CochainComplex FS ℤ :=
  (HomologicalComplex.single FS (ComplexShape.up ℤ) 0).obj (coefficientSheaf p k B σ a)

def coefficientComplexIso :
    ((U).mapHomologicalComplex (ComplexShape.up ℤ)).obj (nativeCoefficientComplex p k B) ≅
      framedCoefficientComplex p k B σ a :=
  (HomologicalComplex.singleMapHomologicalComplex U (ComplexShape.up ℤ) 0).app
    (Site.coefficientSheaf p k X) ≪≫
    (HomologicalComplex.single FS (ComplexShape.up ℤ) 0).mapIso (coefficientIso p k B σ a)

def globalHomEquiv (M : CochainComplex FS ℤ) :
    (DerivedCategory.Q.obj (framedCoefficientComplex p k B σ a) ⟶ DerivedCategory.Q.obj M) ≃
      (DerivedCategory.Q.obj (nativeCoefficientComplex p k B) ⟶
        DerivedCategory.Q.obj (((G).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) :=
  (Iso.homCongr (DerivedCategory.Q.mapIso (coefficientComplexIso p k B σ a)).symm (Iso.refl _)).trans
    (DerivedAdjunction.FramedCrystallineDerivedAdjunction.homEquiv p k B σ a (nativeCoefficientComplex p k B) M)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.DerivedSections.FramedCrystallineDerivedSections
