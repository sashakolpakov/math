import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.HomologyPreservationCompose
import OAI.AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Affine Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.AffineHomology

noncomputable section

/-! Native base-linear sections on an affine open preserve the homology
of quasicoherent complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S) (U : X.Opens)

abbrev sections : X.Modules ⥤ ModuleCat.{u} Γ(S, ⊤) :=
  AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π ⋙
    (CategoryTheory.evaluation X.Opensᵒᵖ (ModuleCat.{u} Γ(S, ⊤))).obj (op U)

def coefficientMap : Γ(S, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp π.appTop.hom

theorem preservesLeft (hU : IsAffineOpen U) (T : ShortComplex X.Modules)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent] :
    (sections π U).PreservesLeftHomologyOf T := by
  have := Affine.ModuleHomology.preservesLeft U hU T
  change (Affine.ModuleExactSections.sections U ⋙
    ModuleCat.restrictScalars (coefficientMap π U)).PreservesLeftHomologyOf T
  exact HomologyPreservationCompose.left (Affine.ModuleExactSections.sections U)
    (ModuleCat.restrictScalars (coefficientMap π U)) T

theorem quasiIso (hU : IsAffineOpen U)
    {K L : CochainComplex X.Modules ℕ} (f : K ⟶ L)
    [∀ n, (K.X n).IsQuasicoherent] [∀ n, (L.X n).IsQuasicoherent] [QuasiIso f] :
    QuasiIso (((sections π U).mapHomologicalComplex (.up ℕ)).map f) := by
  constructor
  intro n
  have : (K.sc n).X₁.IsQuasicoherent := inferInstanceAs (K.X ((ComplexShape.up ℕ).prev n)).IsQuasicoherent
  have : (K.sc n).X₂.IsQuasicoherent := inferInstanceAs (K.X n).IsQuasicoherent
  have : (K.sc n).X₃.IsQuasicoherent := inferInstanceAs (K.X ((ComplexShape.up ℕ).next n)).IsQuasicoherent
  have : (L.sc n).X₁.IsQuasicoherent := inferInstanceAs (L.X ((ComplexShape.up ℕ).prev n)).IsQuasicoherent
  have : (L.sc n).X₂.IsQuasicoherent := inferInstanceAs (L.X n).IsQuasicoherent
  have : (L.sc n).X₃.IsQuasicoherent := inferInstanceAs (L.X ((ComplexShape.up ℕ).next n)).IsQuasicoherent
  have : (sections π U).PreservesLeftHomologyOf (K.sc n) := preservesLeft π U hU (K.sc n)
  have : (sections π U).PreservesLeftHomologyOf (L.sc n) := preservesLeft π U hU (L.sc n)
  have : ShortComplex.QuasiIso ((HomologicalComplex.shortComplexFunctor X.Modules (.up ℕ) n).map f) :=
    (quasiIsoAt_iff f n).mp inferInstance
  rw [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_map_of_preservesLeftHomology (sections π U)
    ((HomologicalComplex.shortComplexFunctor X.Modules (.up ℕ) n).map f)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.AffineHomology
