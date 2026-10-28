import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ExteriorBases
import OAI.AlgebraicGeometry.Comparison.Betti.FreeSheafHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-! # Exterior Quasicoherent -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.ExteriorQuasicoherent

noncomputable section

/-! The actual exterior-form module sheaves are quasicoherent on standard smooth affine charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]

section Basis

variable {ι : Type} [LinearOrder ι]
  (b : Module.Basis ι (ExteriorRestrictions.globalCoordinateAlgebra X) Ω[ExteriorRestrictions.globalCoordinateAlgebra X⁄ℂ])

def affineExteriorFreeIso (n : ℕ) :
    SheafOfModules.free (R := X.left.ringCatSheaf) (Set.powersetCard ι n) ≅
      Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n := by
  let q : FreeSheafHom.sheafifiedFree (Opens.grothendieckTopology X.left)
      X.left.ringCatSheaf (Set.powersetCard ι n) ⟶ Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n :=
    (PresheafOfModules.sheafification.{0} (R := X.left.ringCatSheaf)
      (𝟙 X.left.ringCatSheaf.obj)).map
        (Betti.Module.FrameBases.Frames.frame X.left.ringCatSheaf (Exterior.ModuleSheaf.exteriorFormsModulePresheaf X n)
          (ExteriorBases.globalExteriorGenerators X b n))
  have : IsIso q := ExteriorBases.exteriorFrameSheafification_isIso X b n
  exact (FreeSheafHom.sheafifiedFreeIso (Opens.grothendieckTopology X.left)
    X.left.ringCatSheaf (Set.powersetCard ι n)).symm ≪≫
      asIso q

include b in
theorem exteriorFormsModuleSheaf_quasicoherent (n : ℕ) :
    (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).prop_of_iso (affineExteriorFreeIso X b n)
    inferInstance

end Basis

theorem standardSmooth_exteriorFormsModuleSheaf_quasicoherent
    [Algebra.IsStandardSmooth ℂ (ExteriorRestrictions.globalCoordinateAlgebra X)] (n : ℕ) :
    (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n).IsQuasicoherent := by
  classical
  let : LinearOrder (Module.Free.ChooseBasisIndex (ExteriorRestrictions.globalCoordinateAlgebra X)
      Ω[ExteriorRestrictions.globalCoordinateAlgebra X⁄ℂ]) := linearOrderOfSTO WellOrderingRel
  exact exteriorFormsModuleSheaf_quasicoherent X
    (Module.Free.chooseBasis (ExteriorRestrictions.globalCoordinateAlgebra X) Ω[ExteriorRestrictions.globalCoordinateAlgebra X⁄ℂ]) n

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.ExteriorQuasicoherent
