import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.DualUnitClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ClassCoefficientNaturality

/-! # Dual Class Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.DualClassScalars

noncomputable section

/-! Multiplication of the literal first-order coefficients by a
global regular scalar gives the original algebraic H1 scalar action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem regularDualUnitClass_scalar (X : Scheme.{0}) {I : Type} (U : I → X.Opens) (hU : iSup U = ⊤)
    (u v : Dual.UnitCechCoefficients.DualUnitCechCoefficients X.sheaf.obj U) (hu : Dual.UnitCechCoefficients.DualUnitCechNormalized X.sheaf.obj U u)
    (hv : Dual.UnitCechCoefficients.DualUnitCechNormalized X.sheaf.obj U v) (hcu : Dual.UnitCechCoefficients.DualUnitCechCocycle X.sheaf.obj U u)
    (hcv : Dual.UnitCechCoefficients.DualUnitCechCocycle X.sheaf.obj U v) (r : Γ(X, ⊤))
    (he : ∀ a : Fin 2 → I, (v a).val.snd =
      X.presheaf.map (homOfLE (show AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a ≤ ⊤ from le_top)).op r *
        (show Γ(X, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) from (u a).val.snd)) :
    let : Module Γ(X, ⊤) (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X) 1) :=
      SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule (HilbertConstruction.Line.Bundles.structureModule X) 1
    DualUnitClass.regularDualUnitClass X U hU v hv hcv = r • DualUnitClass.regularDualUnitClass X U hU u hu hcu := by
  let : Module Γ(X, ⊤) (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X) 1) :=
    SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule (HilbertConstruction.Line.Bundles.structureModule X) 1
  let f : Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf ⟶ Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf :=
    (SheafOfModules.toSheaf X.ringCatSheaf).map (SheafCohomology.AffineH.Projective.globalSmulHom (HilbertConstruction.Line.Bundles.structureModule X) r)
  have hc : Dual.UnitCechCoefficients.dualUnitCechAdditive X.sheaf.obj U v =
      DivisorClass.Chern.Abelian.CechClasses.abelianCechCoefficient U f.hom 1 (Dual.UnitCechCoefficients.dualUnitCechAdditive X.sheaf.obj U u) := by
    funext a
    exact he a
  have h := Cech.ClassCoefficientNaturality.cechSheafClass_eq_map_of_coefficient U f hU 0 _ _
    (Dual.UnitCechCoefficients.dualUnitCechAdditive_closed X.sheaf.obj U u hu hcu) (Dual.UnitCechCoefficients.dualUnitCechAdditive_closed X.sheaf.obj U v hv hcv) hc
  exact h.trans (SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule_smul (HilbertConstruction.Line.Bundles.structureModule X) 1 r
    (DualUnitClass.regularDualUnitClass X U hU u hu hcu)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.DualClassScalars
