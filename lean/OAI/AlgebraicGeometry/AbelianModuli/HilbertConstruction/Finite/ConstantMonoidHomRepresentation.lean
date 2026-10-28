import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantMonoidHomParameters

/-! # Constant Monoid Hom Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantMonoidHomRepresentation

noncomputable section

/-! Finite-constant homomorphisms form a naturally represented functor with an actual native universal homomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} [IsNoetherian S] (A : Over S) [IsProper A.hom]
variable (I : Type u) [Fintype I] [MonObj A] [MonObj (ConstantScheme.Iff.constantScheme S I)]

def finiteConstantMonoidHomSubfunctor : Subfunctor (Geometric.MorphismFunctor.geometricFamilyMorphismFunctor (ConstantScheme.Iff.constantScheme S I) A) where
  obj _ := {f | IsMonHom f}
  map c f hf := by
    apply (ParameterPullbackMonoidIso.geometricFamilyMorphismBaseChange_isMonHom_iff c.unop f).mpr
    exact (MappedMonoidHomEquations.mappedMonoidHom_iff (Over.pullback c.unop.left) f).mpr
      ⟨congrArg (Over.pullback c.unop.left).map hf.one_hom,
        congrArg (Over.pullback c.unop.left).map hf.mul_hom⟩

def finiteConstantMonoidHomFunctor : (Over S)ᵒᵖ ⥤ Type u :=
  (finiteConstantMonoidHomSubfunctor A I).toFunctor

def finiteConstantMonoidHomClassifyingIso :
    yoneda.obj (ConstantMonoidHomParameters.finiteConstantMonoidHomParameter A I) ≅ finiteConstantMonoidHomFunctor A I :=
  NatIso.ofComponents (fun T => (ConstantMonoidHomParameters.finiteConstantMonoidHomParameterPointEquiv A I T.unop).toIso) (by
    intro T U c
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    change (ConstantMonoidHomParameters.finiteConstantMonoidHomParameterPointEquiv A I U.unop (c.unop ≫ p)).val =
      Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c.unop (ConstantMonoidHomParameters.finiteConstantMonoidHomParameterPointEquiv A I T.unop p).val
    rw [ConstantMonoidHomParameters.finiteConstantMonoidHomParameterPointEquiv_val, ConstantMonoidHomParameters.finiteConstantMonoidHomParameterPointEquiv_val]
    exact (congrArg (ConstantMorphismParameters.finiteConstantMorphismParameterPointEquiv A I U.unop)
      (Category.assoc c.unop p (ConstantMonoidHomParameters.finiteConstantMonoidHomParameterInclusion A I))).trans
        (ConstantMorphismParameters.finiteConstantMorphismParameterPointEquiv_natural A I c.unop
          (p ≫ ConstantMonoidHomParameters.finiteConstantMonoidHomParameterInclusion A I)))

instance finiteConstantMonoidHomParameter_proper : IsProper (ConstantMonoidHomParameters.finiteConstantMonoidHomParameter A I).hom := by
  rw [← (ConstantMonoidHomParameters.finiteConstantMonoidHomParameterInclusion A I).w]
  infer_instance

instance finiteConstantMonoidHomParameter_noetherian : IsNoetherian (ConstantMonoidHomParameters.finiteConstantMonoidHomParameter A I).left :=
  FamilyPower.properSource_noetherian (ConstantMonoidHomParameters.finiteConstantMonoidHomParameter A I).hom

def finiteConstantMonoidHomParameterProjective (P : Projective.ProjectivePresentations.ProjectivePresentation A)
    (x : 𝟙_ (Over S) ⟶ A) [IsClosedImmersion x.left] :
    Projective.ProjectivePresentations.ProjectivePresentation (ConstantMonoidHomParameters.finiteConstantMonoidHomParameter A I) :=
  (ConstantMorphismParameters.finiteConstantMorphismParameterProjective A I P x).ofClosedImmersion
    (ConstantMonoidHomParameters.finiteConstantMonoidHomParameterInclusion A I)

def finiteConstantMonoidHomUniversal : ConstantMonoidHomParameters.FiniteConstantMonoidHom A I (ConstantMonoidHomParameters.finiteConstantMonoidHomParameter A I) :=
  ConstantMonoidHomParameters.finiteConstantMonoidHomParameterPointEquiv A I _ (𝟙 _)

theorem finiteConstantMonoidHomUniversal_point {T : Over S}
    (p : T ⟶ ConstantMonoidHomParameters.finiteConstantMonoidHomParameter A I) :
    (ConstantMonoidHomParameters.finiteConstantMonoidHomParameterPointEquiv A I T p).val =
      Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange p (finiteConstantMonoidHomUniversal A I).val := by
  have h := ConcreteCategory.congr_hom (CC := fun X : Type u => X)
    ((finiteConstantMonoidHomClassifyingIso A I).hom.naturality p.op) (𝟙 _)
  change ConstantMonoidHomParameters.finiteConstantMonoidHomParameterPointEquiv A I T (p ≫ 𝟙 _) =
    (finiteConstantMonoidHomFunctor A I).map p.op (finiteConstantMonoidHomUniversal A I) at h
  rw [Category.comp_id] at h
  exact congrArg Subtype.val h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantMonoidHomRepresentation
