import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Resolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution

/-! # Sheaf Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution

noncomputable section

/-!
# The native crystalline structure sheaf resolved by a polynomial frame

Exact coefficient lifting and sheafification carry the frame-coordinate
presheaf resolution to an actual resolution of the native structure sheaf.
The transition maps retain the fixed polynomial frame coordinates.
-/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution.CrystallinePolynomialSheafResolution

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B) [Fintype σ]

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution.CrystallinePolynomialSheafResolution.Sheaves p k X

def complex : CochainComplex V ℕ :=
  ((PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (Resolution.CrystallineFrameResolution.complex p k B σ a)

def augmentation : (CochainComplex.single₀ V).obj (Site.structureSheaf p k X) ⟶
    complex p k B σ a :=
  (CochainComplex.single₀ V).map (PolynomialSheafResolution.CrystallinePolynomialSheafResolution.coefficientIso p k X).inv ≫
    (HomologicalComplex.singleMapHomologicalComplex (PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X) (ComplexShape.up ℕ) 0).inv.app
      (Site.functions p k X) ≫
    ((PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (Resolution.CrystallineFrameResolution.augmentation p k B σ a)

instance augmentation_quasiIso : QuasiIso (augmentation p k B σ a) := by
  have hmap : QuasiIso (((PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (Resolution.CrystallineFrameResolution.augmentation p k B σ a)) := by infer_instance
  have hinner : QuasiIso
      ((HomologicalComplex.singleMapHomologicalComplex (PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X) (ComplexShape.up ℕ) 0).inv.app
        (Site.functions p k X) ≫
        ((PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (Resolution.CrystallineFrameResolution.augmentation p k B σ a)) := quasiIso_comp
    ((HomologicalComplex.singleMapHomologicalComplex (PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X) (ComplexShape.up ℕ) 0).inv.app
      (Site.functions p k X))
    (((PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (Resolution.CrystallineFrameResolution.augmentation p k B σ a))
  exact quasiIso_comp ((CochainComplex.single₀ V).map (PolynomialSheafResolution.CrystallinePolynomialSheafResolution.coefficientIso p k X).inv) _ (hφ' := hinner)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution
