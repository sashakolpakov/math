import OAI.AlgebraicGeometry.Resolution.Blowups.Open.AffineBoundaryRestriction

/-! # Named Affine Section Map -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.NamedAffineSectionMap.Construction

noncomputable section

/-! Section algebra maps with a fixed, independently named complex structure on the source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
  (q : Y ⟶ X) (hq : q ≫ f = g)

def affineOpenSectionAlgMapTo (U : X.affineOpens) (V : Y.affineOpens) (h : V.1 ≤ q ⁻¹ᵁ U.1) :
    letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
    letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra g V
    Γ(X, U) →ₐ[ℂ] Γ(Y, V) := by
  let : Algebra ℂ Γ(X, U) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : Algebra ℂ Γ(Y, V) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra g V
  exact { toRingHom := (q.appLE U.1 V.1 h).hom
          commutes' := fun c => RingHom.congr_fun ((Affine.ComplexNaturality.Construction.affineComplexScalars_appLE f q V U h).trans
            (congrArg (fun t => Affine.ComplexNaturality.Construction.affineComplexScalars t V) hq)) c }

end

end OAI.AlgebraicGeometry.Resolution.Blowups.NamedAffineSectionMap.Construction
