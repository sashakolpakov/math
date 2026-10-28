import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantMonoidIsoParameters

/-! # Constant Monoid Iso Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantMonoidIsoRepresentation

noncomputable section

/-! Isomorphisms from a finite constant group form a naturally represented functor under actual geometric base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} [IsNoetherian S] (A : Over S) [IsProper A.hom]
variable (I : Type u) [Fintype I] [MonObj A] [MonObj (ConstantScheme.Iff.constantScheme S I)]

def finiteConstantMonoidIsoSubfunctor : Subfunctor (ConstantMonoidHomRepresentation.finiteConstantMonoidHomFunctor A I) where
  obj _ := {f | IsIso f.val}
  map c f hf := by
    have : IsIso f.val := hf
    exact (Geometric.MorphismIsomorphisms.geometricFamilyMorphismBaseChange_isIso_iff c.unop f.val).mpr
      ((Over.pullback c.unop.left).map_isIso f.val)

def finiteConstantMonoidIsoFunctor : (Over S)ᵒᵖ ⥤ Type u :=
  (finiteConstantMonoidIsoSubfunctor A I).toFunctor

theorem finiteConstantMonoidHomParameterPointEquiv_natural {U T : Over S} (c : U ⟶ T)
    (p : T ⟶ ConstantMonoidHomParameters.finiteConstantMonoidHomParameter A I) :
    ConstantMonoidHomParameters.finiteConstantMonoidHomParameterPointEquiv A I U (c ≫ p) =
      (ConstantMonoidHomRepresentation.finiteConstantMonoidHomFunctor A I).map c.op (ConstantMonoidHomParameters.finiteConstantMonoidHomParameterPointEquiv A I T p) :=
  ConcreteCategory.congr_hom (CC := fun X : Type u => X)
    ((ConstantMonoidHomRepresentation.finiteConstantMonoidHomClassifyingIso A I).hom.naturality c.op) p

def finiteConstantMonoidIsoClassifyingIso :
    yoneda.obj (ConstantMonoidIsoParameters.finiteConstantMonoidIsoParameter A I) ≅ finiteConstantMonoidIsoFunctor A I :=
  NatIso.ofComponents (fun T => (ConstantMonoidIsoParameters.finiteConstantMonoidIsoParameterPointEquiv A I T.unop).toIso) (by
    intro T U c
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    change (ConstantMonoidIsoParameters.finiteConstantMonoidIsoParameterPointEquiv A I U.unop (c.unop ≫ p)).val =
      (ConstantMonoidHomRepresentation.finiteConstantMonoidHomFunctor A I).map c (ConstantMonoidIsoParameters.finiteConstantMonoidIsoParameterPointEquiv A I T.unop p).val
    rw [ConstantMonoidIsoParameters.finiteConstantMonoidIsoParameterPointEquiv_val, ConstantMonoidIsoParameters.finiteConstantMonoidIsoParameterPointEquiv_val]
    exact (congrArg (ConstantMonoidHomParameters.finiteConstantMonoidHomParameterPointEquiv A I U.unop)
      (Category.assoc c.unop p (ConstantMonoidIsoParameters.finiteConstantMonoidIsoParameterInclusion A I))).trans
        (finiteConstantMonoidHomParameterPointEquiv_natural A I c.unop
          (p ≫ ConstantMonoidIsoParameters.finiteConstantMonoidIsoParameterInclusion A I)))

theorem finiteConstantMonoidIso_quasiProjective_representation (P : Projective.ProjectivePresentations.ProjectivePresentation A)
    (x : 𝟙_ (Over S) ⟶ A) [IsClosedImmersion x.left] :
    ∃ M : Over S, Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation M) ∧
      Nonempty (finiteConstantMonoidIsoFunctor A I ≅ yoneda.obj M) :=
  ⟨ConstantMonoidIsoParameters.finiteConstantMonoidIsoParameter A I,
    ⟨ConstantMonoidIsoParameters.finiteConstantMonoidIsoParameterQuasiProjectivePresentation A I P x⟩,
    ⟨(finiteConstantMonoidIsoClassifyingIso A I).symm⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantMonoidIsoRepresentation
