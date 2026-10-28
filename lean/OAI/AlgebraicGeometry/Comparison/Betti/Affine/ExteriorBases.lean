import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ExteriorRestrictions
import OAI.AlgebraicGeometry.Comparison.Betti.Module.FrameBases

/-! # Exterior Bases -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.ExteriorBases

noncomputable section

/-! Actual exterior bases on basic opens, obtained by localizing a differential basis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
  {ι : Type} [LinearOrder ι]
  (b : Module.Basis ι (ExteriorRestrictions.globalCoordinateAlgebra X) Ω[ExteriorRestrictions.globalCoordinateAlgebra X⁄ℂ])

def basicExteriorBasis (r : ExteriorRestrictions.globalCoordinateAlgebra X) (n : ℕ) :
    Module.Basis (Set.powersetCard ι n) (ExteriorRestrictions.basicCoordinateAlgebra X r)
      (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.Forms (ExteriorRestrictions.basicCoordinateAlgebra X r) n) := by
  let := ((Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℂ X).map (ExteriorRestrictions.basicOpenRestriction X r)).hom.toRingHom.toAlgebra
  have : Module.Free (ExteriorRestrictions.globalCoordinateAlgebra X) Ω[ExteriorRestrictions.globalCoordinateAlgebra X⁄ℂ] :=
    Module.Free.of_basis b
  have : IsLocalization (Submonoid.powers r) (ExteriorRestrictions.basicCoordinateAlgebra X r) :=
    ExteriorRestrictions.basicCoordinateAlgebra_isLocalization X r
  exact ((isLocalizedModule_iff_isBaseChange (Submonoid.powers r) (ExteriorRestrictions.basicCoordinateAlgebra X r)
    (ExteriorRestrictions.basicExteriorRestriction X r n)).mp (ExteriorRestrictions.basicExteriorRestriction_isLocalizedModule X r n)).basis
      (b.exteriorPower n)

theorem basicExteriorBasis_apply (r : ExteriorRestrictions.globalCoordinateAlgebra X) (n : ℕ)
    (i : Set.powersetCard ι n) :
    basicExteriorBasis X b r n i = ExteriorRestrictions.basicExteriorRestriction X r n (b.exteriorPower n i) := by
  simp only [basicExteriorBasis, IsBaseChange.basis_apply]

def globalExteriorGenerators (n : ℕ) :
    Set.powersetCard ι n → (Exterior.ModuleSheaf.exteriorFormsModulePresheaf X n).obj (op ⊤) := b.exteriorPower n

omit [IsAffine X.left] in
theorem exteriorModuleRestriction_apply (r : ExteriorRestrictions.globalCoordinateAlgebra X) (n : ℕ)
    (ω : (Exterior.ModuleSheaf.exteriorFormsModulePresheaf X n).obj (op ⊤)) :
    (Exterior.ModuleSheaf.exteriorFormsModulePresheaf X n).map (ExteriorRestrictions.basicOpenRestriction X r) ω =
      ExteriorRestrictions.basicExteriorRestriction X r n ω := rfl

theorem exteriorFrame_basic_isIso (r : ExteriorRestrictions.globalCoordinateAlgebra X) (n : ℕ) :
    IsIso ((Betti.Module.FrameBases.Frames.frame X.left.ringCatSheaf (Exterior.ModuleSheaf.exteriorFormsModulePresheaf X n)
      (globalExteriorGenerators X b n)).app (op (X.left.basicOpen r))) := by
  let c : Module.Basis (Set.powersetCard ι n)
      (X.left.ringCatSheaf.obj.obj (op (X.left.basicOpen r)))
      ((Exterior.ModuleSheaf.exteriorFormsModulePresheaf X n).obj (op (X.left.basicOpen r))) := basicExteriorBasis X b r n
  apply Betti.Module.FrameBases.Frames.frame_app_isIso X.left.ringCatSheaf (Exterior.ModuleSheaf.exteriorFormsModulePresheaf X n)
    (globalExteriorGenerators X b n) (op (X.left.basicOpen r)) c
  intro i
  exact (basicExteriorBasis_apply X b r n i).symm

theorem exteriorFrameSheafification_isIso (n : ℕ) :
    IsIso ((PresheafOfModules.sheafification.{0} (R := X.left.ringCatSheaf)
      (𝟙 X.left.ringCatSheaf.obj)).map
        (Betti.Module.FrameBases.Frames.frame X.left.ringCatSheaf (Exterior.ModuleSheaf.exteriorFormsModulePresheaf X n)
          (globalExteriorGenerators X b n))) := by
  apply Betti.Module.FrameBases.Frames.sheafified_frame_isIso X.left.ringCatSheaf
    (Exterior.ModuleSheaf.exteriorFormsModulePresheaf X n) (globalExteriorGenerators X b n) (isBasis_basicOpen X.left)
  intro U hU
  obtain ⟨r, rfl⟩ := hU
  exact exteriorFrame_basic_isIso X b r n

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.ExteriorBases
