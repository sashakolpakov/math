import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.SheafBoundaries
import OAI.AlgebraicGeometry.SheafCohomology.Cech

/-! # Acyclic Cech Boundary Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AcyclicCechBoundaryDetection

noncomputable section

/-! A zero class on an actual acyclic cover has a primitive on that
same cover. For the structure sheaf of a separated scheme, an affine
cover supplies the required acyclicity in every positive degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.TopCat.Sheaf
open OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.SheafBoundaries OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)

theorem abelianCechToSheaf_eq_acyclicIso (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (hU : iSup U = ⊤) (hH : SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U F) (n : ℕ) :
    DivisorClass.Chern.Abelian.CechComparison.abelianCechToSheaf U F hU n =
      (SheafCohomology.Cech.Comparison.TopCat.Sheaf.cechHomologySuccIsoOfAcyclicIntersections U F hU hH n).hom := by
  unfold DivisorClass.Chern.Abelian.CechComparison.abelianCechToSheaf DivisorClass.Chern.Abelian.CechComparison.abelianCechToDerived SheafCohomology.Cech.Comparison.TopCat.Sheaf.cechHomologySuccIsoOfAcyclicIntersections
    SheafCohomology.Cech.Comparison.TopCat.Sheaf.cechPositiveRightDerivedIso SheafCohomology.Cech.Comparison.TopCat.Sheaf.cechPositiveVerticalHomologyIso
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  rfl

theorem cech_boundary_of_acyclic_sheaf_class_zero
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (hU : iSup U = ⊤)
    (hH : SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U F) (n : ℕ)
    (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F.obj U (n + 1))
    (hk : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U (n + 1) k = 0)
    (hclass : DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U F hU n k hk =
      (0 : (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1) :
        _ ⥤ AddCommGrpCat.{0}).obj F)) :
    ∃ b : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F.obj U n, DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U n b = k := by
  let K := (CategoryTheory.cechComplexFunctor U).obj F.obj
  let x := (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F.obj U (n + 1)).symm k
  have hx : K.d (n + 1) (n + 2) x = 0 := DivisorClass.Chern.Abelian.CechClasses.abelianCechNative_closed U F.obj (n + 1) k hk
  have hz : DivisorClass.Chern.Abelian.CechClasses.abelianCechNativeClass U F.obj n k hk = 0 := by
    apply (AddCommGrpCat.mono_iff_injective
      (SheafCohomology.Cech.Comparison.TopCat.Sheaf.cechHomologySuccIsoOfAcyclicIntersections U F hU hH n).hom).mp inferInstance
    rw [map_zero, ← abelianCechToSheaf_eq_acyclicIso U F hU hH n]
    exact hclass
  obtain ⟨b, hb⟩ := SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.exists_boundary_of_homologyπ_abCyclesMk_eq_zero n K x hx hz
  refine ⟨DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F.obj U n b, ?_⟩
  have he := congrArg (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F.obj U (n + 1)) hb
  rw [DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates_d] at he
  exact he.trans ((DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F.obj U (n + 1)).apply_symm_apply k)

theorem affine_cech_boundary_of_sheaf_class_zero {Y : Scheme.{0}} [Y.IsSeparated]
    (M : Y.Modules) [M.IsQuasicoherent] {J : Type} (V : J → Y.Opens)
    (hV : iSup V = ⊤) (ha : ∀ i, IsAffineOpen (V i)) (n : ℕ)
    (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M).obj V (n + 1))
    (hk : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M).obj V (n + 1) k = 0)
    (hclass : DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass V ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M) hV n k hk =
      (0 : (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y.carrier) (n + 1) :
        _ ⥤ AddCommGrpCat.{0}).obj ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M))) :
    ∃ b : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M).obj V n,
      DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M).obj V n b = k :=
  cech_boundary_of_acyclic_sheaf_class_zero V _ hV
    (SheafCohomology.Cech.Projective.affineCoverIntersectionsAcyclic M V ha) n k hk hclass

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AcyclicCechBoundaryDetection
