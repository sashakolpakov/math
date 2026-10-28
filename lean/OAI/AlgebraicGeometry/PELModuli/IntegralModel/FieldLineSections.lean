import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineCechBaseChange
import OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Field Line Sections -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldLineSections

noncomputable section

/-! Compare the actual base-ring and Γ(Spec R) section modules, then prove
field-extension invariance of the native global-section dimensions used
in the graph Hilbert bound. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

namespace PolarizationEmbedding

open OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineCechBaseChange.FieldBaseChange
universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (M : X.Modules)

def baseRingSectionsAddEquiv :
    ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op ⊤) ≃+
      (SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).obj M := AddEquiv.refl _

theorem baseRingSectionsAddEquiv_smul (r : R)
    (m : ((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op ⊤)) :
    baseRingSectionsAddEquiv f M (r • m) =
      (Scheme.ΓSpecIso (.of R)).inv r • baseRingSectionsAddEquiv f M m := by
  let : Module Γ(X, ⊤) Γ(M, ⊤) := (M.val.obj (op ⊤)).isModule
  let act : Γ(X, ⊤) → Γ(M, ⊤) → Γ(M, ⊤) := fun a z => a • z
  change act (X.presheaf.map (𝟙 (op ⊤)) (f.appTop ((Scheme.ΓSpecIso (.of R)).inv r))) m =
    act (f.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) m
  rw [X.presheaf.map_id]
  rfl

theorem baseRingSections_finrank :
    Module.finrank R (((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf f).obj M).obj.obj (op ⊤)) =
      Module.finrank Γ(Spec (.of R), ⊤) ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor f).obj M) := by
  exact congrArg Cardinal.toNat (rank_eq_of_equiv_equiv
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm
    (baseRingSectionsAddEquiv f M)
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.bijective
    (baseRingSectionsAddEquiv_smul f M))

theorem fieldLineSections_baseChange_finrank {k K : Type u} [Field k] [Field K] [Algebra k K]
    {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k)) [IsSeparated π] [QuasiCompact π]
    (L : Y.Modules) (hL : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle L) :
    Module.finrank Γ(Spec (.of K), ⊤)
      ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (pullback.snd π (FieldAffineSections.FieldBaseChange.affineBaseChangeMap k K))).obj
        ((Scheme.Modules.pullback (pullback.fst π (FieldAffineSections.FieldBaseChange.affineBaseChangeMap k K))).obj L)) =
      Module.finrank Γ(Spec (.of k), ⊤) ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor π).obj L) := by
  calc
    _ = Module.finrank K ((LineCechBaseChange.FieldBaseChange.lineBundleBaseChangedCoefficients K π L).obj.obj (op ⊤)) :=
      (baseRingSections_finrank (pullback.snd π (FieldAffineSections.FieldBaseChange.affineBaseChangeMap k K))
        ((Scheme.Modules.pullback (pullback.fst π (FieldAffineSections.FieldBaseChange.affineBaseChangeMap k K))).obj L)).symm
    _ = Module.finrank K (K ⊗[k] (((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf π).obj L).obj.obj (op ⊤))) :=
      (LineCechBaseChange.FieldBaseChange.lineBundleFlatBaseChangeGlobalSectionsEquiv K π L hL).finrank_eq.symm
    _ = Module.finrank k (((FieldSectionModules.FieldBaseChange.modulesAsBaseRingSheaf π).obj L).obj.obj (op ⊤)) :=
      Module.finrank_baseChange
    _ = _ := baseRingSections_finrank π L

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldLineSections
