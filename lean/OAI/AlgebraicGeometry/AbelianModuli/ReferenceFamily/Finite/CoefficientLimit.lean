import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CoefficientSpecLimit
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LimitBaseChange

/-! # Coefficient Limit -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CoefficientLimit

noncomputable section

/-! Constant families over arbitrary coefficient spectra are actual
inverse limits of their families over finite-type coefficient spectra. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable (k : Type u) [CommRing k]

def algebraSpecOver (R : Type u) [CommRing R] [Algebra k R] : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R)))

def algebraSpecMap {R T : Type u} [CommRing R] [CommRing T] [Algebra k R] [Algebra k T]
    (f : R →ₐ[k] T) : algebraSpecOver k T ⟶ algebraSpecOver k R :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k T))
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact f.commutes x)

variable (R : Type u) [CommRing R] [Algebra k R]

def finiteCoefficientOverDiagram : (Finset R)ᵒᵖ ⥤ Over (Spec (.of k)) where
  obj s := algebraSpecOver k (CoefficientDiagram.finiteCoefficientRing k R s.unop)
  map {s t} f := algebraSpecMap k (Subalgebra.inclusion
    (Algebra.adjoin_mono (show (t.unop : Set R) ⊆ (s.unop : Set R) from leOfHom f.unop)))
  map_id s := by
    apply Over.OverMorphism.ext
    change Spec.map (𝟙 (.of (CoefficientDiagram.finiteCoefficientRing k R s.unop))) = 𝟙 _
    exact Spec.map_id _
  map_comp f g := by
    apply Over.OverMorphism.ext
    dsimp only [algebraSpecMap]
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    congr 1

def finiteCoefficientOverCone : Cone (finiteCoefficientOverDiagram k R) where
  pt := algebraSpecOver k R
  π := {
    app s := algebraSpecMap k (CoefficientDiagram.finiteCoefficientRing k R s.unop).val
    naturality := by
      intro s t f
      apply Over.OverMorphism.ext
      change _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp]
      congr 1 }

def finiteCoefficientOverConeUnderlying_isLimit :
    IsLimit ((Over.forget (Spec (.of k))).mapCone (finiteCoefficientOverCone k R)) :=
  CoefficientSpecLimit.finiteCoefficientSpecCone_isLimit k R

def finiteCoefficientFamilyCone (X : Over (Spec (.of k))) :
    Cone (finiteCoefficientOverDiagram k R ⋙ Over.pullback X.hom ⋙ Over.forget X.left) := by
  classical
  exact LimitBaseChange.baseChangedSchemeCone X.hom (finiteCoefficientOverCone k R)

def finiteCoefficientFamilyCone_isLimit (X : Over (Spec (.of k))) :
    IsLimit (finiteCoefficientFamilyCone k R X) := by
  classical
  exact LimitBaseChange.baseChangedSchemeCone_isLimit X.hom (finiteCoefficientOverCone k R)
    (finiteCoefficientOverConeUnderlying_isLimit k R)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CoefficientLimit
