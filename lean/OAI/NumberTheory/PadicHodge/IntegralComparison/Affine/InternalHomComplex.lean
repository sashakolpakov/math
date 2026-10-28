import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.InternalHom
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.Algebra.Homology.Additive

/-! # Internal Hom Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.InternalHomComplex

noncomputable section

/-! The actual affine internal-Hom section comparison, including all
differentials of a complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R]

local notation "Γₐ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.InternalHom.sections (R := R)

instance sections_additive : (Γₐ).Additive where
  map_add {_M _N} _f _g := rfl

variable (N : (Spec (CommRingCat.of R)).Modules)

def sectionHom : (Spec (CommRingCat.of R)).Modulesᵒᵖ ⥤ ModuleCat R :=
  SchemeInternalHom.functor N ⋙ Γₐ

def algebraicHom : (Spec (CommRingCat.of R)).Modulesᵒᵖ ⥤ ModuleCat R :=
  (Γₐ).op ⋙ (linearYoneda R (ModuleCat R)).obj ((Γₐ).obj N)

instance sectionHom_additive : (sectionHom N).Additive := by
  unfold sectionHom
  infer_instance

instance algebraicHom_additive : (algebraicHom N).Additive := by
  unfold algebraicHom
  infer_instance

def comparison : sectionHom N ⟶ algebraicHom N where
  app M := ModuleCat.ofHom (R := R) (X := (sectionHom N).obj M)
    (Y := (algebraicHom N).obj M) (InternalHom.evaluation M.unop N)
  naturality {M P} f := by
    ext q
    exact InternalHom.precomp P.unop N f.unop q

theorem comparison_isIso (M : (Spec (CommRingCat.of R)).Modulesᵒᵖ)
    [M.unop.IsQuasicoherent] : IsIso ((comparison N).app M) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (InternalHom.evaluation_bijective M.unop N)

def complexMap {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex (Spec (CommRingCat.of R)).Modulesᵒᵖ c) :
    ((sectionHom N).mapHomologicalComplex c).obj K ⟶
      ((algebraicHom N).mapHomologicalComplex c).obj K :=
  ((comparison N).mapHomologicalComplex c).app K

theorem complexMap_isIso {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex (Spec (CommRingCat.of R)).Modulesᵒᵖ c)
    [∀ i, (K.X i).unop.IsQuasicoherent] : IsIso (complexMap N c K) := by
  let (i : ι) : IsIso ((complexMap N c K).f i) := comparison_isIso N (K.X i)
  exact HomologicalComplex.Hom.isIso_of_components _

def complexIso {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex (Spec (CommRingCat.of R)).Modulesᵒᵖ c)
    [∀ i, (K.X i).unop.IsQuasicoherent] :
    ((sectionHom N).mapHomologicalComplex c).obj K ≅
      ((algebraicHom N).mapHomologicalComplex c).obj K := by
  letI := complexMap_isIso N c K
  exact asIso (complexMap N c K)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.InternalHomComplex
