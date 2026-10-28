import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IsoParameters

/-! # Iso Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IsoRepresentation

noncomputable section

/-! Bounded abelian isomorphisms form a natural subfunctor represented by the constructed quasi-projective open parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {g h n : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
variable (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable (P : Polynomial ℚ)

def boundedAbelianIsoSubfunctor : Subfunctor (MonoidHomRepresentation.boundedFamilyMonoidHomFunctor j P) where
  obj _ := {f | IsIso f.val.val}
  map c f hf := by
    apply (Geometric.MorphismIsomorphisms.geometricFamilyMorphismBaseChange_isIso_iff c.unop f.val.val).mpr
    let e := @asIso _ _ _ _ f.val.val hf
    exact inferInstanceAs (IsIso ((Over.pullback c.unop.left).mapIso e).hom)

def boundedAbelianIsoFunctor : (Over S)ᵒᵖ ⥤ Type u := (boundedAbelianIsoSubfunctor A B j P).toFunctor

def boundedAbelianIsoClassifyingIso :
    yoneda.obj (IsoParameters.boundedAbelianIsoParameter A B j P) ≅ boundedAbelianIsoFunctor A B j P :=
  NatIso.ofComponents (fun T => (IsoParameters.boundedAbelianIsoParameterPointEquiv A B j P T.unop).toIso) (by
    intro T U c
    apply ConcreteCategory.hom_ext
    intro y
    apply Subtype.ext
    change (IsoParameters.boundedAbelianIsoParameterPointEquiv A B j P U.unop (c.unop ≫ y)).val =
      (MonoidHomRepresentation.boundedFamilyMonoidHomFunctor j P).map c (IsoParameters.boundedAbelianIsoParameterPointEquiv A B j P T.unop y).val
    rw [IsoParameters.boundedAbelianIsoParameterPointEquiv_val, IsoParameters.boundedAbelianIsoParameterPointEquiv_val, Category.assoc]
    exact HomFiberFaithfulness.boundedFamilyMonoidHomPoint_natural j P c.unop (y ≫ IsoParameters.boundedAbelianIsoParameterInclusion A B j P))

theorem boundedAbelianIso_quasiProjective_representation :
    ∃ M : Over S, Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation M) ∧
      Nonempty (boundedAbelianIsoFunctor A B j P ≅ yoneda.obj M) :=
  ⟨IsoParameters.boundedAbelianIsoParameter A B j P, ⟨IsoParameters.boundedAbelianIsoParameterQuasiProjectivePresentation A B j P⟩,
    ⟨(boundedAbelianIsoClassifyingIso A B j P).symm⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IsoRepresentation
