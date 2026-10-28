import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.OpenRestriction
import OAI.AlgebraicGeometry.Comparison.Betti.ManifoldHolomorphicModuleSheaf
import Mathlib.Topology.Sheaves.Module

/-! # Unit Frame -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.UnitFrame.Dolbeault

noncomputable section

section

/-! A unit trivialization on the over-site identifies the literal restricted
additive sheaf with the native holomorphic function sheaf on the open manifold. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable {M : TopCat.{0}}

abbrev moduleAdditiveSheaf (R : TopCat.Sheaf RingCat.{0} M) (F : SheafOfModules.{0} R) :
    TopCat.Sheaf AddCommGrpCat.{0} M := ⟨F.val.presheaf, F.isSheaf⟩

def openUnitTrivializationSheafIso (R : TopCat.Sheaf RingCat.{0} M)
    (F : SheafOfModules.{0} R) (U : Opens M)
    (e : F.over U ≅ SheafOfModules.unit.{0} (R.over U)) :
    (SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat.{0} U.isOpenEmbedding).obj
        (moduleAdditiveSheaf R F) ≅
      (SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat.{0} U.isOpenEmbedding).obj
        (moduleAdditiveSheaf R (SheafOfModules.unit.{0} R)) :=
  (U.sheafEquivOver (A := AddCommGrpCat.{0})).functor.mapIso
    ((SheafOfModules.toSheaf.{0} (R.over U)).mapIso e)

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E M]

def nativeHolomorphicUnitSheafIso :
    (SheafOfModules.toSheaf.{0} (ManifoldHolomorphicModuleSheaf.manifoldHolomorphicStructureSheaf E M)).obj
        (SheafOfModules.unit.{0} (ManifoldHolomorphicModuleSheaf.manifoldHolomorphicStructureSheaf E M)) ≅
      DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M := Iso.refl _

def holomorphicOpenUnitTrivializationSheafIso
    (F : SheafOfModules.{0} (ManifoldHolomorphicModuleSheaf.manifoldHolomorphicStructureSheaf E M))
    (U : Opens M)
    (e : F.over U ≅ SheafOfModules.unit.{0} ((ManifoldHolomorphicModuleSheaf.manifoldHolomorphicStructureSheaf E M).over U)) :
    (SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat.{0} U.isOpenEmbedding).obj
        ((SheafOfModules.toSheaf.{0} (ManifoldHolomorphicModuleSheaf.manifoldHolomorphicStructureSheaf E M)).obj F) ≅
      DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E U :=
  openUnitTrivializationSheafIso (ManifoldHolomorphicModuleSheaf.manifoldHolomorphicStructureSheaf E M) F U e ≪≫
    (SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat.{0} U.isOpenEmbedding).mapIso (nativeHolomorphicUnitSheafIso E) ≪≫
      Holomorphic.OpenRestriction.Dolbeault.holomorphicFunctionSheaf_restrictIso U

end

section

/-! Evaluating an actual open unit frame gives the original section-space
coordinate map, without introducing a new choice of coefficients. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {M : TopCat.{0}} (R : TopCat.Sheaf RingCat.{0} M)
  (F : SheafOfModules.{0} R) (U : Opens M)
  (e : F.over U ≅ SheafOfModules.unit.{0} (R.over U))

def openUnitFrameSectionIso :
    F.val.obj (op U) ≅ (SheafOfModules.unit.{0} R).val.obj (op U) :=
  (SheafOfModules.evaluation (R := R.over U) (op (Over.mk (𝟙 U)))).mapIso e

def openUnitFrameSectionEquiv :
    F.val.obj (op U) ≃ₗ[R.obj.obj (op U)] R.obj.obj (op U) :=
  (openUnitFrameSectionIso R F U e).toLinearEquiv

theorem openUnitFrameSectionEquiv_apply (a : F.val.obj (op U)) :
    openUnitFrameSectionEquiv R F U e a = e.hom.val.app (op (Over.mk (𝟙 U))) a := rfl

end

/-! Unit-frame coordinates commute with transport along equality of open domains. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {M : TopCat.{0}} (R : TopCat.Sheaf RingCat.{0} M) (F : SheafOfModules.{0} R)

def transportOpenUnitFrame {U V : Opens M} (h : U = V)
    (e : F.over V ≅ SheafOfModules.unit.{0} (R.over V)) :
    F.over U ≅ SheafOfModules.unit.{0} (R.over U) := h.symm ▸ e

theorem transportOpenUnitFrame_heq {U V : Opens M} (h : U = V)
    (e : F.over V ≅ SheafOfModules.unit.{0} (R.over V)) :
    HEq (transportOpenUnitFrame R F h e) e := by
  subst V
  rfl

theorem openUnitFrameSectionEquiv_domain_transport {U V : Opens M} (h : U = V)
    (e : F.over V ≅ SheafOfModules.unit.{0} (R.over V)) (a : F.val.obj (op U)) :
    R.obj.map (homOfLE h.ge).op (openUnitFrameSectionEquiv R F U (transportOpenUnitFrame R F h e) a) =
      openUnitFrameSectionEquiv R F V e (F.val.map (homOfLE h.ge).op a) := by
  subst V
  simp only [homOfLE_refl, op_id]
  erw [F.val.map_id]
  change R.obj.map (𝟙 (op U)) (openUnitFrameSectionEquiv R F U e a) =
    openUnitFrameSectionEquiv R F U e a
  rw [R.obj.map_id]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.UnitFrame.Dolbeault
