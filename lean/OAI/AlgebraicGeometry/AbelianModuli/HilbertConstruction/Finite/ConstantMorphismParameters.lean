import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FamilyPowers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.FamilyMorphismLabels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismFunctor

/-! # Constant Morphism Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantMorphismParameters

noncomputable section

/-! Maps from a finite constant family into a pointed projective family are naturally represented by a concrete finite power of that family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} (A : Over S) (I : Type u) [Fintype I]

def finiteConstantMorphismParameter : Over S := FamilyPowers.finiteLabelFamilyPower A I

def finiteConstantMorphismParameterPointEquiv (T : Over S) :
    (T ⟶ finiteConstantMorphismParameter A I) ≃
      ((Over.pullback T.hom).obj (ConstantScheme.Iff.constantScheme S I) ⟶ (Over.pullback T.hom).obj A) :=
  (FamilyPowers.finiteLabelFamilyPowerPoints A I T).trans (Constant.FamilyMorphismLabels.constantFamilyMorphismLabelsEquiv A I T).symm

theorem finiteConstantMorphismParameterPointEquiv_labels (T : Over S)
    (p : T ⟶ finiteConstantMorphismParameter A I) :
    Constant.FamilyMorphismLabels.constantFamilyMorphismLabelsEquiv A I T (finiteConstantMorphismParameterPointEquiv A I T p) =
      FamilyPowers.finiteLabelFamilyPowerPoints A I T p :=
  (Constant.FamilyMorphismLabels.constantFamilyMorphismLabelsEquiv A I T).apply_symm_apply _

theorem finiteConstantMorphismParameterPointEquiv_natural {U T : Over S} (c : U ⟶ T)
    (p : T ⟶ finiteConstantMorphismParameter A I) :
    finiteConstantMorphismParameterPointEquiv A I U (c ≫ p) =
      Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c (finiteConstantMorphismParameterPointEquiv A I T p) := by
  apply (Constant.FamilyMorphismLabels.constantFamilyMorphismLabelsEquiv A I U).injective
  funext i
  rw [finiteConstantMorphismParameterPointEquiv_labels, Constant.FamilyMorphismLabels.constantFamilyMorphismLabelsEquiv_natural,
    finiteConstantMorphismParameterPointEquiv_labels]
  exact FamilyPowers.finiteFamilyPowerPoints_natural A (Fintype.card I) c p (Fintype.equivFin I i)

def finiteConstantMorphismClassifyingIso :
    yoneda.obj (finiteConstantMorphismParameter A I) ≅ Geometric.MorphismFunctor.geometricFamilyMorphismFunctor (ConstantScheme.Iff.constantScheme S I) A :=
  NatIso.ofComponents (fun T => (finiteConstantMorphismParameterPointEquiv A I T.unop).toIso) (by
    intro T U c
    apply ConcreteCategory.hom_ext
    intro p
    exact finiteConstantMorphismParameterPointEquiv_natural A I c.unop p)

def finiteConstantMorphismParameterProjective (P : Projective.ProjectivePresentations.ProjectivePresentation A)
    (x : 𝟙_ (Over S) ⟶ A) [IsClosedImmersion x.left] :
    Projective.ProjectivePresentations.ProjectivePresentation (finiteConstantMorphismParameter A I) :=
  FamilyPowers.finiteFamilyPowerProjective A P x (Fintype.card I)

def finiteConstantUniversalMorphism :
    (Over.pullback (finiteConstantMorphismParameter A I).hom).obj (ConstantScheme.Iff.constantScheme S I) ⟶
      (Over.pullback (finiteConstantMorphismParameter A I).hom).obj A :=
  finiteConstantMorphismParameterPointEquiv A I _ (𝟙 _)

theorem finiteConstantUniversalMorphism_point {T : Over S}
    (p : T ⟶ finiteConstantMorphismParameter A I) :
    finiteConstantMorphismParameterPointEquiv A I T p =
      Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange p (finiteConstantUniversalMorphism A I) := by
  have h := finiteConstantMorphismParameterPointEquiv_natural A I p (𝟙 _)
  rw [Category.comp_id] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantMorphismParameters
