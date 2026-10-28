import OAI.AlgebraicGeometry.FormalGeometry.Completion.CommBaseChange
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Algebras -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.Algebras.Construction

noncomputable section

/-!
# Completion: affine objects in the actual pro-étale site

Weakly étale commutative algebras map contravariantly to the actual site
by their spectra. This embeds the affine algebra description fully faithfully.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (R : Type u) [CommRing R]

/-- The actual geometric weakly étale condition on a commutative algebra. -/
def weaklyEtaleAlgebra : ObjectProperty (CommAlgCat.{u} R) :=
  fun A => WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap R A)))

abbrev ProEtaleAlgebra := (weaklyEtaleAlgebra R).FullSubcategory

instance (A : ProEtaleAlgebra R) :
    WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap R A.obj))) := A.property

/-- The spectrum of a weakly étale algebra as an actual site object. -/
def proEtaleAlgebraSpec : (ProEtaleAlgebra R)ᵒᵖ ⥤ (Spec (CommRingCat.of R)).ProEt where
  obj A := Scheme.ProEt.mk (Spec.map (CommRingCat.ofHom (algebraMap R A.unop.obj)))
  map f := MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom)) (by
    erw [← Spec.map_comp]
    congr 1
    ext r
    exact f.unop.hom.hom.commutes r)
  map_id A := by
    apply MorphismProperty.Over.Hom.ext
    exact Spec.map_id _
  map_comp f g := by
    apply MorphismProperty.Over.Hom.ext
    exact Spec.map_comp (CommRingCat.ofHom g.unop.hom.hom.toRingHom)
      (CommRingCat.ofHom f.unop.hom.hom.toRingHom)

variable {R}

/-- A morphism between affine site objects determines its actual map of base algebras. -/
def proEtaleAlgebraHomOfSpec {A B : ProEtaleAlgebra R}
    (f : (proEtaleAlgebraSpec R).obj (op A) ⟶ (proEtaleAlgebraSpec R).obj (op B)) : B ⟶ A := by
  let g := Spec.preimage f.left
  have hg : CommRingCat.ofHom (algebraMap R B.obj) ≫ g =
      CommRingCat.ofHom (algebraMap R A.obj) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact MorphismProperty.Over.w f
  exact ObjectProperty.homMk (CommAlgCat.ofHom
    { __ := g.hom
      commutes' r := congrArg (fun h : CommRingCat.of R ⟶ CommRingCat.of A.obj => h r) hg })

/-- Spectrum is fully faithful on the actual weakly étale algebras. -/
def proEtaleAlgebraSpecFullyFaithful : (proEtaleAlgebraSpec R).FullyFaithful where
  preimage f := (proEtaleAlgebraHomOfSpec f).op
  map_preimage f := by
    apply MorphismProperty.Over.Hom.ext
    exact Spec.map_preimage _
  preimage_map f := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    ext a
    exact congrArg (fun h => h.hom a)
      (Spec.preimage_map (CommRingCat.ofHom f.unop.hom.hom.toRingHom))

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.Algebras.Construction
