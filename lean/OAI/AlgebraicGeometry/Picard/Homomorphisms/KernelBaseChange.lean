import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGroup
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! # Kernel Base Change -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelBaseChange

noncomputable section

/-! Formation of the scheme-theoretic kernel commutes with arbitrary base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S T : Scheme.{u}} {A B : Over S} [GrpObj B]

omit [GrpObj B] in
def equalizerRightCongrIso (f g g' : A ⟶ B) (h : g = g') :
    equalizer f g ≅ equalizer f g' := by
  subst g'
  exact Iso.refl _

omit [GrpObj B] in
theorem equalizerRightCongrIso_inclusion (f g g' : A ⟶ B) (h : g = g') :
    (equalizerRightCongrIso f g g' h).hom ≫ equalizer.ι f g' = equalizer.ι f g := by
  subst g'
  simp [equalizerRightCongrIso]

def kernelBaseChangeIso (s : T ⟶ S) (q : A ⟶ B) :
    (Over.pullback s).obj (Kernel.Construction.kernelScheme q) ≅ Kernel.Construction.kernelScheme ((Over.pullback s).map q) :=
  PreservesEqualizer.iso (Over.pullback s) q (1 : A ⟶ B) ≪≫
    equalizerRightCongrIso _ _ _ (Functor.map_one (Over.pullback s))

theorem kernelBaseChangeIso_inclusion (s : T ⟶ S) (q : A ⟶ B) :
    (kernelBaseChangeIso s q).hom ≫ Kernel.Construction.kernelInclusion ((Over.pullback s).map q) =
      (Over.pullback s).map (Kernel.Construction.kernelInclusion q) := by
  change (_ ≫ _) ≫ equalizer.ι _ _ = _
  rw [Category.assoc]
  have h := equalizerRightCongrIso_inclusion ((Over.pullback s).map q)
    ((Over.pullback s).map (1 : A ⟶ B)) 1 (Functor.map_one (Over.pullback s))
  exact (congrArg (fun z => (PreservesEqualizer.iso (Over.pullback s) q 1).hom ≫ z) h).trans
    (by simp [Kernel.Construction.kernelInclusion]; rfl)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelBaseChange
