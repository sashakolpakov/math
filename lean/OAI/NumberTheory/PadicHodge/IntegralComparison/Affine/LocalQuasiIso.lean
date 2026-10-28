import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.Detection
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CoherentHomology
import Mathlib.Algebra.Homology.QuasiIso

/-! # Local Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LocalQuasiIso

noncomputable section

/-! A map of quasicoherent complexes is a quasi-isomorphism whenever
the actual section complexes on an affine open cover have that property. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u v

variable {X : Scheme.{u}} {ι : Type v} {c : ComplexShape ι}

theorem homology_quasicoherent (K : HomologicalComplex X.Modules c)
    [∀ i, (K.X i).IsQuasicoherent] (n : ι) : (K.homology n).IsQuasicoherent := by
  let : (K.sc n).X₁.IsQuasicoherent := inferInstanceAs (K.X (c.prev n)).IsQuasicoherent
  let : (K.sc n).X₂.IsQuasicoherent := inferInstanceAs (K.X n).IsQuasicoherent
  let : (K.sc n).X₃.IsQuasicoherent := inferInstanceAs (K.X (c.next n)).IsQuasicoherent
  exact Module.CoherentHomology.quasicoherent (K.sc n)

variable {K L : HomologicalComplex X.Modules c}
  [∀ i, (K.X i).IsQuasicoherent] [∀ i, (L.X i).IsQuasicoherent]
  (a : K ⟶ L)

theorem section_homology_isIso (U : X.Opens) (hU : IsAffineOpen U) (n : ι)
    [QuasiIso (((ModuleExactSections.sections U).mapHomologicalComplex c).map a)] :
    IsIso ((ModuleExactSections.sections U).map (HomologicalComplex.homologyMap a n)) := by
  let F := ModuleExactSections.sections U
  let : (K.sc n).X₁.IsQuasicoherent := inferInstanceAs (K.X (c.prev n)).IsQuasicoherent
  let : (K.sc n).X₂.IsQuasicoherent := inferInstanceAs (K.X n).IsQuasicoherent
  let : (K.sc n).X₃.IsQuasicoherent := inferInstanceAs (K.X (c.next n)).IsQuasicoherent
  let : (L.sc n).X₁.IsQuasicoherent := inferInstanceAs (L.X (c.prev n)).IsQuasicoherent
  let : (L.sc n).X₂.IsQuasicoherent := inferInstanceAs (L.X n).IsQuasicoherent
  let : (L.sc n).X₃.IsQuasicoherent := inferInstanceAs (L.X (c.next n)).IsQuasicoherent
  let : F.PreservesLeftHomologyOf (K.sc n) := ModuleHomology.preservesLeft U hU (K.sc n)
  let : F.PreservesLeftHomologyOf (L.sc n) := ModuleHomology.preservesLeft U hU (L.sc n)
  let b := (HomologicalComplex.shortComplexFunctor X.Modules c n).map a
  have hn := ShortComplex.mapHomologyIso_hom_naturality b F
  let : IsIso (ShortComplex.homologyMap (F.mapShortComplex.map b)) :=
    (quasiIsoAt_iff_isIso_homologyMap ((F.mapHomologicalComplex c).map a) n).mp inferInstance
  have : IsIso ((K.sc n).mapHomologyIso F).hom := inferInstance
  have : IsIso (((K.sc n).mapHomologyIso F).hom ≫ F.map (ShortComplex.homologyMap b)) := by
    rw [← hn]
    infer_instance
  change IsIso (F.map (ShortComplex.homologyMap b))
  exact IsIso.of_isIso_comp_left ((K.sc n).mapHomologyIso F).hom _

theorem of_cover {τ : Type u} (U : τ → X.Opens) (hU : iSup U = ⊤)
    (hAffine : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, QuasiIso (((ModuleExactSections.sections (U i)).mapHomologicalComplex c).map a)) :
    QuasiIso a := by
  constructor
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let := homology_quasicoherent K n
  let := homology_quasicoherent L n
  apply AffineSection.Detection.cover (HomologicalComplex.homologyMap a n) U hU hAffine
  intro i
  let := h i
  exact section_homology_isIso a (U i) (hAffine i) n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LocalQuasiIso
