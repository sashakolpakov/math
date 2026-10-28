import OAI.AlgebraicGeometry.SheafCohomology.SectionFrames
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.CategoryTheory.Sites.Spaces

/-! # Line Bundle Local Generators -/

namespace OAI.AlgebraicGeometry.SheafCohomology.LineBundleLocalGenerators.Projective

noncomputable section

section

/-! Rank-one generators and frames for free sheaf modules. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{0}) [HasWeakSheafify J AddCommGrpCat.{0}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{0}]

def rankOneFreeIso (M : SheafOfModules.{0} R) (e : M ≅ SheafOfModules.unit R) :
    SheafOfModules.free (R := R) PUnit ≅ M :=
  coproductUniqueIso (fun _ : PUnit => SheafOfModules.unit R) ≪≫ e.symm

def rankOneGenerators (M : SheafOfModules.{0} R) (e : M ≅ SheafOfModules.unit R) :
    M.GeneratingSections :=
  (SheafOfModules.free.generatingSections PUnit).ofEpi (rankOneFreeIso R M e).hom

set_option backward.isDefEq.respectTransparency false in
instance rankOneGenerators_isIso (M : SheafOfModules.{0} R)
    (e : M ≅ SheafOfModules.unit R) : IsIso (rankOneGenerators R M e).π := by
  unfold rankOneGenerators
  rw [SheafOfModules.GeneratingSections.ofEpi_π,
    SheafOfModules.free.generatingSections_π]
  change IsIso (𝟙 (SheafOfModules.free (R := R) PUnit) ≫ (rankOneFreeIso R M e).hom)
  rw [Category.id_comp]
  infer_instance

instance rankOneGenerators_finite (M : SheafOfModules.{0} R)
    (e : M ≅ SheafOfModules.unit R) : (rankOneGenerators R M e).IsFiniteType where
  finite := inferInstanceAs (Finite PUnit)

end

/-! Local generators and local freeness of the actual ProjectiveCohomology line-bundle sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

def lineBundleLocalGenerators (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : Sheaves.Projective.LineBundle A) :
    L.sheaf.LocalGeneratorsData where
  I := A.carrier
  X := L.trivializingOpen
  coversTop := by
    rw [Opens.coversTop_iff]
    apply IsOpenCover.mk
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, L.mem_trivializingOpen x⟩
  generators x := rankOneGenerators _ _
    (SectionFrames.Projective.chosenSectionFrameOver A L x (L.trivializingOpen x) le_rfl)

instance lineBundleLocalGenerators_locallyFree (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : Sheaves.Projective.LineBundle A) :
    (lineBundleLocalGenerators A L).IsLocallyFreeData where
  isIso _x := rankOneGenerators_isIso _ _ _

/-- Local triviality of the actual sheaf gives local freeness in the sheaf API. -/
instance lineBundleSheaf_locallyFree (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : Sheaves.Projective.LineBundle A) :
    L.sheaf.IsLocallyFree :=
  (lineBundleLocalGenerators A L).isLocallyFree

end

end OAI.AlgebraicGeometry.SheafCohomology.LineBundleLocalGenerators.Projective
