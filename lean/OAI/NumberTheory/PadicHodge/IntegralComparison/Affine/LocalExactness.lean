import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CoherentHomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BasicOpenAnnihilation
import Mathlib.Algebra.Category.Grp.Limits

/-! # Local Exactness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LocalExactness

noncomputable section

/-! Exactness of a quasicoherent sheaf complex can be checked on the
actual section complexes of an affine open cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u v w

variable {X : Scheme.{u}} {ι : Type v} {c : ComplexShape ι}
  (K : HomologicalComplex X.Modules c) [∀ n, (K.X n).IsQuasicoherent]

def sectionComplex (U : X.Opens) :=
  (((ModuleExactSections.sections U ⋙ forget₂ _ AddCommGrpCat).mapHomologicalComplex c).obj K)

def homologyIso (U : X.Opens) (hU : IsAffineOpen U) (n : ι) :
    (sectionComplex K U).homology n ≅
      (forget₂ (ModuleCat Γ(X, U)) AddCommGrpCat).obj
        ((ModuleExactSections.sections U).obj (K.homology n)) := by
  let F := ModuleExactSections.sections U
  let G := forget₂ (ModuleCat Γ(X, U)) AddCommGrpCat
  let J := (F.mapHomologicalComplex c).obj K
  have : (K.sc n).X₁.IsQuasicoherent := inferInstanceAs (K.X (c.prev n)).IsQuasicoherent
  have : (K.sc n).X₂.IsQuasicoherent := inferInstanceAs (K.X n).IsQuasicoherent
  have : (K.sc n).X₃.IsQuasicoherent := inferInstanceAs (K.X (c.next n)).IsQuasicoherent
  exact (J.sc n).mapHomologyIso G ≪≫ G.mapIso (ModuleHomology.iso U hU (K.sc n))

theorem exactAt_of_cover {τ : Type w} (U : τ → X.Opens) (hcover : iSup U = ⊤)
    (haffine : ∀ i, IsAffineOpen (U i)) (n : ι)
    (hexact : ∀ i, (sectionComplex K (U i)).ExactAt n) : K.ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have : (K.sc n).X₁.IsQuasicoherent := inferInstanceAs (K.X (c.prev n)).IsQuasicoherent
  have : (K.sc n).X₂.IsQuasicoherent := inferInstanceAs (K.X n).IsQuasicoherent
  have : (K.sc n).X₃.IsQuasicoherent := inferInstanceAs (K.X (c.next n)).IsQuasicoherent
  have : (K.homology n).IsQuasicoherent := Module.CoherentHomology.quasicoherent (K.sc n)
  apply AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.ZeroOpenCover.module_isZero_of_restrict_cover U hcover (K.homology n)
  intro i
  apply (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BasicOpenAnnihilation.module_restrict_isZero_iff_sections_subsingleton
    (K.homology n) (U i) (haffine i)).mpr
  exact AddCommGrpCat.subsingleton_of_isZero ((homologyIso K (U i) (haffine i) n).isZero_iff.mp
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (hexact i)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LocalExactness
