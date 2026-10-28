import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.InternalHomComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.HomologyPreservationCompose
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Spec Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.SpecHomology

noncomputable section

/-! The actual R-linear affine section functor preserves the homology of
quasicoherent complexes on Spec R. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R]

abbrev sections := InternalHom.sections (R := R)

def coefficientMap : R →+* Γ(Spec (CommRingCat.of R), ⊤) :=
  ((Spec (CommRingCat.of R)).presheaf.map (𝟙 (op ⊤))).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem preservesLeft (T : ShortComplex (Spec (CommRingCat.of R)).Modules)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent] :
    sections.PreservesLeftHomologyOf T := by
  have := ModuleHomology.preservesLeft ⊤ (isAffineOpen_top _) T
  change (ModuleExactSections.sections ⊤ ⋙
    ModuleCat.restrictScalars (coefficientMap (R := R))).PreservesLeftHomologyOf T
  exact HomologyPreservationCompose.left (ModuleExactSections.sections ⊤)
    (ModuleCat.restrictScalars (coefficientMap (R := R))) T

theorem quasiIso {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (Spec (CommRingCat.of R)).Modules c} (f : K ⟶ L)
    [∀ n, (K.X n).IsQuasicoherent] [∀ n, (L.X n).IsQuasicoherent] [QuasiIso f] :
    QuasiIso (((sections (R := R)).mapHomologicalComplex c).map f) := by
  constructor
  intro n
  have : (K.sc n).X₁.IsQuasicoherent := inferInstanceAs (K.X (c.prev n)).IsQuasicoherent
  have : (K.sc n).X₂.IsQuasicoherent := inferInstanceAs (K.X n).IsQuasicoherent
  have : (K.sc n).X₃.IsQuasicoherent := inferInstanceAs (K.X (c.next n)).IsQuasicoherent
  have : (L.sc n).X₁.IsQuasicoherent := inferInstanceAs (L.X (c.prev n)).IsQuasicoherent
  have : (L.sc n).X₂.IsQuasicoherent := inferInstanceAs (L.X n).IsQuasicoherent
  have : (L.sc n).X₃.IsQuasicoherent := inferInstanceAs (L.X (c.next n)).IsQuasicoherent
  have : sections.PreservesLeftHomologyOf (K.sc n) := preservesLeft (K.sc n)
  have : sections.PreservesLeftHomologyOf (L.sc n) := preservesLeft (L.sc n)
  have : ShortComplex.QuasiIso ((HomologicalComplex.shortComplexFunctor _ c n).map f) :=
    (quasiIsoAt_iff f n).mp inferInstance
  rw [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_map_of_preservesLeftHomology sections
    ((HomologicalComplex.shortComplexFunctor _ c n).map f)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.SpecHomology
