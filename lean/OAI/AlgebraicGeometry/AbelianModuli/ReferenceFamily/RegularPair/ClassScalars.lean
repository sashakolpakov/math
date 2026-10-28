import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Closed
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ClassCoefficientNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.TermModules
import OAI.AlgebraicGeometry.SheafCohomology.AffineH

/-! # Class Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassScalars

noncomputable section

/-! Multiplication of original regular pair cocycles by a global
function gives the native global-functions action on algebraic H1. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Scheme.{0}) {I : Type} (U : I → X.Opens) (hU : iSup U = ⊤)
    (v w : ∀ i j : I, Γ(X, U i ⊓ U j))
    (hv : Closed.RegularPairCocycle X U v) (hw : Closed.RegularPairCocycle X U w)

theorem regularPairSheafClass_globalScalar (r : Γ(X, ⊤))
    (he : ∀ i j : I, w i j =
      X.presheaf.map (homOfLE (show U i ⊓ U j ≤ ⊤ from le_top)).op r * v i j) :
    let : Module Γ(X, ⊤) (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X) 1) :=
      SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule (HilbertConstruction.Line.Bundles.structureModule X) 1
    Closed.regularPairSheafClass X U hU w hw = r •
      (show SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X) 1 from Closed.regularPairSheafClass X U hU v hv) := by
  let : Module Γ(X, ⊤) (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule X) 1) :=
    SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule (HilbertConstruction.Line.Bundles.structureModule X) 1
  let f : Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf ⟶ Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf :=
    (SheafOfModules.toSheaf X.ringCatSheaf).map (SheafCohomology.AffineH.Projective.globalSmulHom (HilbertConstruction.Line.Bundles.structureModule X) r)
  have hc : Closed.regularPairCechCochain X U w =
      DivisorClass.Chern.Abelian.CechClasses.abelianCechCoefficient U f.hom 1 (Closed.regularPairCechCochain X U v) := by
    funext a
    have h := congrArg (fun s => X.presheaf.map (homOfLE
      (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1))).op s)
      (he (a 0) (a 1))
    rw [map_mul, Closed.regularSectionRestrict_comp] at h
    exact h
  have h := Cech.ClassCoefficientNaturality.cechSheafClass_eq_map_of_coefficient U f hU 0 _ _
    (Closed.regularPairCechCochain_closed X U v hv) (Closed.regularPairCechCochain_closed X U w hw) hc
  exact h.trans (SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule_smul (HilbertConstruction.Line.Bundles.structureModule X) 1 r
    (Closed.regularPairSheafClass X U hU v hv)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassScalars
