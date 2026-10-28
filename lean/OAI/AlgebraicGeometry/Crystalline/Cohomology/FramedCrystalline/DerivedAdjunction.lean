import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.ExactAdjunction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactDerived

/-! # Derived Adjunction -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.DerivedAdjunction.FramedCrystallineDerivedAdjunction

noncomputable section

/-!
# The derived adjunction for the actual crystalline frame site

Both sheaf functors have proved exactness for the native Witt-module
coefficients. Their adjunction therefore passes to the actual derived
categories. The resulting hom-set equivalence applies to arbitrary
complexes of native and framed crystalline sheaves.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafPushforward.CrystallineFrameSheafPushforward.Coefficients p k
local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.ExactAdjunction.FramedCrystallineExactAdjunction.restriction p k B σ a
local notation "G" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.ExactAdjunction.FramedCrystallineExactAdjunction.frame p k B σ a

abbrev NativeSheaves := Sheaf (Site.topology p k X) V
abbrev FramedSheaves := Sheaf (Topology.FramedCrystallineTopology.native p k B σ a) V

local instance nativeDerived : HasDerivedCategory.{u + 2} (NativeSheaves p k B) :=
  HasDerivedCategory.standard _

local instance framedDerived : HasDerivedCategory.{u + 2} (FramedSheaves p k B σ a) :=
  HasDerivedCategory.standard _

def restriction : DerivedCategory (NativeSheaves p k B) ⥤ DerivedCategory (FramedSheaves p k B σ a) :=
  ExactDerived.ExactDerivedAdjunction.map U

def frame : DerivedCategory (FramedSheaves p k B σ a) ⥤ DerivedCategory (NativeSheaves p k B) :=
  ExactDerived.ExactDerivedAdjunction.map G

def adjunction : restriction p k B σ a ⊣ frame p k B σ a :=
  ExactDerived.ExactDerivedAdjunction.onDerived
    (Topology.FramedCrystallineTopology.sheafAdjunction p k B σ a V (Site.topology p k X))

def homEquiv (L : CochainComplex (NativeSheaves p k B) ℤ)
    (M : CochainComplex (FramedSheaves p k B σ a) ℤ) :
    (DerivedCategory.Q.obj (((U).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ⟶ DerivedCategory.Q.obj M) ≃
      (DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj (((G).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) :=
  (Iso.homCongr ((ExactDerived.ExactDerivedAdjunction.mapFactors U).app L).symm (Iso.refl _)).trans
    (((adjunction p k B σ a).homEquiv (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)).trans
      (Iso.homCongr (Iso.refl _) ((ExactDerived.ExactDerivedAdjunction.mapFactors G).app M)))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.DerivedAdjunction.FramedCrystallineDerivedAdjunction
