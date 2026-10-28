import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.MonoidHomParameters

/-! # Monoid Hom Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.MonoidHomRepresentation

noncomputable section

/-! The actual bounded family-homomorphism functor is naturally represented by the constructed quasi-projective closed parameter, with a native universal homomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {A B : Over S} {n : ℕ}
variable [IsProper A.hom] [Smooth A.hom] [IsSeparated B.hom] [MonObj A] [MonObj B]
variable (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (P : Polynomial ℚ)

def boundedFamilyMonoidHomSubfunctor : Subfunctor (EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor j P) where
  obj _ := {f | IsMonHom f.val}
  map c f hf := by
    have : IsMonHom f.val := hf
    apply (ParameterPullbackMonoidIso.geometricFamilyMorphismBaseChange_isMonHom_iff c.unop f.val).mpr
    exact (MappedMonoidHomEquations.mappedMonoidHom_iff (Over.pullback c.unop.left) f.val).mpr
      ⟨congrArg (Over.pullback c.unop.left).map hf.one_hom,
        congrArg (Over.pullback c.unop.left).map hf.mul_hom⟩

def boundedFamilyMonoidHomFunctor : (Over S)ᵒᵖ ⥤ Type u :=
  (boundedFamilyMonoidHomSubfunctor j P).toFunctor

def boundedFamilyMonoidHomClassifyingIso :
    yoneda.obj (MonoidHomParameters.boundedFamilyMonoidHomParameter j P) ≅ boundedFamilyMonoidHomFunctor j P :=
  NatIso.ofComponents (fun T => (MonoidHomParameters.boundedFamilyMonoidHomParameterPointEquiv j P T.unop).toIso) (by
    intro T U c
    apply ConcreteCategory.hom_ext
    intro y
    apply Subtype.ext
    change (MonoidHomParameters.boundedFamilyMonoidHomParameterPointEquiv j P U.unop (c.unop ≫ y)).val =
      (EmbeddedMorphismFunctor.boundedEmbeddedMorphismFunctor j P).map c
        (MonoidHomParameters.boundedFamilyMonoidHomParameterPointEquiv j P T.unop y).val
    rw [MonoidHomParameters.boundedFamilyMonoidHomParameterPointEquiv_val, MonoidHomParameters.boundedFamilyMonoidHomParameterPointEquiv_val]
    exact (congrArg (HilbertConstruction.Smooth.GraphParameterPointEquivalence.smoothEmbeddedGraphParameterMorphismEquiv j P U.unop)
      (Category.assoc c.unop y (MonoidHomParameters.boundedFamilyMonoidHomParameterInclusion j P))).trans
        (OperationParameterNaturality.smoothEmbeddedGraphParameterMorphismEquiv_natural j P c.unop
          (y ≫ MonoidHomParameters.boundedFamilyMonoidHomParameterInclusion j P)))

theorem boundedFamilyMonoidHom_quasiProjective_representation :
    ∃ M : Over S, Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation M) ∧
      Nonempty (boundedFamilyMonoidHomFunctor j P ≅ yoneda.obj M) :=
  ⟨MonoidHomParameters.boundedFamilyMonoidHomParameter j P,
    ⟨MonoidHomParameters.boundedFamilyMonoidHomParameterQuasiProjectivePresentation j P⟩,
    ⟨(boundedFamilyMonoidHomClassifyingIso j P).symm⟩⟩

def boundedFamilyMonoidHomUniversal :
    MonoidHomParameters.BoundedFamilyMonoidHom j P (MonoidHomParameters.boundedFamilyMonoidHomParameter j P) :=
  MonoidHomParameters.boundedFamilyMonoidHomParameterPointEquiv j P _ (𝟙 _)

theorem boundedFamilyMonoidHomUniversal_isMonHom :
    IsMonHom (boundedFamilyMonoidHomUniversal j P).val.val :=
  (boundedFamilyMonoidHomUniversal j P).property

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.MonoidHomRepresentation
