import OAI.AlgebraicGeometry.Comparison.Betti.Exterior.OpenSheaf
import OAI.AlgebraicGeometry.Comparison.Betti.Open.ModuleFrames
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ExteriorQuasicoherent
import OAI.AlgebraicGeometry.Comparison.Betti.StandardSmoothBasis

/-! # Exterior Frames -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ExteriorFrames

noncomputable section

section

/-! Actual local frames for exterior-form module sheaves on every smooth complex scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

abbrev exteriorFrameIndex [Algebra.IsStandardSmooth ℂ (Affine.ExteriorRestrictions.globalCoordinateAlgebra X)] (n : ℕ) :=
  Set.powersetCard (Module.Free.ChooseBasisIndex (Affine.ExteriorRestrictions.globalCoordinateAlgebra X)
    Ω[Affine.ExteriorRestrictions.globalCoordinateAlgebra X⁄ℂ]) n

def standardSmoothExteriorFreeIso [IsAffine X.left]
    [Algebra.IsStandardSmooth ℂ (Affine.ExteriorRestrictions.globalCoordinateAlgebra X)] (n : ℕ) :
    SheafOfModules.free (R := X.left.ringCatSheaf) (exteriorFrameIndex X n) ≅
      Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n := by
  classical
  let : LinearOrder (Module.Free.ChooseBasisIndex (Affine.ExteriorRestrictions.globalCoordinateAlgebra X)
      Ω[Affine.ExteriorRestrictions.globalCoordinateAlgebra X⁄ℂ]) := linearOrderOfSTO WellOrderingRel
  exact Affine.ExteriorQuasicoherent.affineExteriorFreeIso X
    (Module.Free.chooseBasis (Affine.ExteriorRestrictions.globalCoordinateAlgebra X) Ω[Affine.ExteriorRestrictions.globalCoordinateAlgebra X⁄ℂ]) n

def standardSmoothOpenFrameIso (U : X.left.Opens) [IsAffine (Open.AffineIsoEvaluation.openOver X U).left]
    [Algebra.IsStandardSmooth ℂ (Affine.ExteriorRestrictions.globalCoordinateAlgebra (Open.AffineIsoEvaluation.openOver X U))] (n : ℕ) :
    SheafOfModules.free (R := X.left.ringCatSheaf.over U)
        (exteriorFrameIndex (Open.AffineIsoEvaluation.openOver X U) n) ≅ (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n).over U :=
  Open.ModuleFrames.Restriction.overFreeIso U (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n)
    (exteriorFrameIndex (Open.AffineIsoEvaluation.openOver X U) n)
      (standardSmoothExteriorFreeIso (Open.AffineIsoEvaluation.openOver X U) n ≪≫
        (Exterior.OpenSheaf.exteriorOpenSheafIso (Open.AffineIsoEvaluation.openInclusion X U) n).symm)

variable [Smooth X.hom]

def standardSmoothChart (x : X.left) : X.left.Opens :=
  (StandardSmoothBasis.exists_standardSmooth_openOver X x).choose

theorem standardSmoothChart_spec (x : X.left) :
    x ∈ standardSmoothChart X x ∧ IsAffine (Open.AffineIsoEvaluation.openOver X (standardSmoothChart X x)).left ∧
      Algebra.IsStandardSmooth ℂ (Affine.ExteriorRestrictions.globalCoordinateAlgebra (Open.AffineIsoEvaluation.openOver X (standardSmoothChart X x))) :=
  (StandardSmoothBasis.exists_standardSmooth_openOver X x).choose_spec

instance standardSmoothChart_affine (x : X.left) :
    IsAffine (Open.AffineIsoEvaluation.openOver X (standardSmoothChart X x)).left :=
  (standardSmoothChart_spec X x).2.1

instance standardSmoothChart_standardSmooth (x : X.left) :
    Algebra.IsStandardSmooth ℂ (Affine.ExteriorRestrictions.globalCoordinateAlgebra (Open.AffineIsoEvaluation.openOver X (standardSmoothChart X x))) :=
  (standardSmoothChart_spec X x).2.2

theorem standardSmoothChart_coversTop :
    (Opens.grothendieckTopology X.left).CoversTop (standardSmoothChart X) := by
  intro W x hxW
  let V := W ⊓ standardSmoothChart X x
  exact ⟨V, homOfLE inf_le_left, ⟨x, ⟨homOfLE inf_le_right⟩⟩,
    ⟨hxW, (standardSmoothChart_spec X x).1⟩⟩

def smoothExteriorChartFrameIso (x : X.left) (n : ℕ) :
    SheafOfModules.free (R := X.left.ringCatSheaf.over (standardSmoothChart X x))
        (exteriorFrameIndex (Open.AffineIsoEvaluation.openOver X (standardSmoothChart X x)) n) ≅
      (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n).over (standardSmoothChart X x) :=
  standardSmoothOpenFrameIso X (standardSmoothChart X x) n

end

/-! The actual exterior-form module sheaves are locally free and of finite type on smooth schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom]

def smoothExteriorChartGenerators (x : X.left) (n : ℕ) :
    ((Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n).over (standardSmoothChart X x)).GeneratingSections := by
  let e := smoothExteriorChartFrameIso X x n
  have : IsIso e.hom := e.isIso_hom
  have : Epi e.hom := CategoryTheory.IsIso.epi_of_iso e.hom
  exact (SheafOfModules.free.generatingSections
    (R := X.left.ringCatSheaf.over (standardSmoothChart X x))
    (exteriorFrameIndex (Open.AffineIsoEvaluation.openOver X (standardSmoothChart X x)) n)).ofEpi e.hom

theorem smoothExteriorChartGenerators_isIso (x : X.left) (n : ℕ) :
    IsIso (smoothExteriorChartGenerators X x n).π := by
  unfold smoothExteriorChartGenerators
  simp only [SheafOfModules.GeneratingSections.ofEpi_π,
    SheafOfModules.free.generatingSections_π]
  exact (smoothExteriorChartFrameIso X x n).isIso_hom

theorem smoothExteriorChartGenerators_finite (x : X.left) (n : ℕ) :
    (smoothExteriorChartGenerators X x n).IsFiniteType where
  finite := inferInstanceAs (Finite (exteriorFrameIndex (Open.AffineIsoEvaluation.openOver X (standardSmoothChart X x)) n))

def smoothExteriorLocalGenerators (n : ℕ) : (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n).LocalGeneratorsData where
  I := X.left
  X := standardSmoothChart X
  coversTop := standardSmoothChart_coversTop X
  generators x := smoothExteriorChartGenerators X x n

instance smoothExteriorLocalGenerators_free (n : ℕ) :
    (smoothExteriorLocalGenerators X n).IsLocallyFreeData where
  isIso x := smoothExteriorChartGenerators_isIso X x n

instance smoothExteriorLocalGenerators_finite (n : ℕ) :
    (smoothExteriorLocalGenerators X n).IsFiniteType where
  isFiniteType x := smoothExteriorChartGenerators_finite X x n

theorem smooth_exteriorFormsModuleSheaf_locallyFree (n : ℕ) :
    (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n).IsLocallyFree :=
  (smoothExteriorLocalGenerators X n).isLocallyFree

theorem smooth_exteriorFormsModuleSheaf_quasicoherent (n : ℕ) :
    (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n).IsQuasicoherent :=
  (smoothExteriorLocalGenerators X n).quasiCoherentData.isQuasicoherent

theorem smooth_exteriorFormsModuleSheaf_finiteType (n : ℕ) :
    (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n).IsFiniteType where
  exists_localGeneratorsData := ⟨smoothExteriorLocalGenerators X n, inferInstance⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ExteriorFrames
