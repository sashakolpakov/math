import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CoefficientDiagram
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Limits.Opposites

/-! # Coefficient Spec Limit -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CoefficientSpecLimit

noncomputable section

/-! The spectrum of an arbitrary coefficient algebra is the actual
inverse limit of its finite-type coefficient spectra. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]

def finiteCoefficientSpecDiagram : (Finset R)ᵒᵖ ⥤ Scheme.{u} :=
  (CoefficientDiagram.finiteCoefficientDiagram k R).op ⋙ Scheme.Spec

def finiteCoefficientSpecCone : Cone (finiteCoefficientSpecDiagram k R) :=
  Scheme.Spec.mapCone (CoefficientDiagram.finiteCoefficientCocone k R).op

def finiteCoefficientSpecCone_isLimit : IsLimit (finiteCoefficientSpecCone k R) :=
  isLimitOfPreserves Scheme.Spec (CoefficientDiagram.finiteCoefficientCocone_isColimit k R).op

theorem finiteCoefficientSpecCone_point : (finiteCoefficientSpecCone k R).pt = Spec (.of R) := rfl

theorem finiteCoefficientSpecCone_projection (s : Finset R) :
    (finiteCoefficientSpecCone k R).π.app (.op s) =
      Spec.map (CommRingCat.ofHom (CoefficientDiagram.finiteCoefficientRing k R s).val.toRingHom) := rfl

instance finiteCoefficientSpecDiagram_affine (s : (Finset R)ᵒᵖ) :
    IsAffine ((finiteCoefficientSpecDiagram k R).obj s) :=
  inferInstanceAs (IsAffine (Spec (.of (CoefficientDiagram.finiteCoefficientRing k R s.unop))))

instance finiteCoefficientSpecDiagram_transitionAffine {s t : (Finset R)ᵒᵖ} (f : s ⟶ t) :
    IsAffineHom ((finiteCoefficientSpecDiagram k R).map f) :=
  isAffineHom_of_isAffine _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CoefficientSpecLimit
