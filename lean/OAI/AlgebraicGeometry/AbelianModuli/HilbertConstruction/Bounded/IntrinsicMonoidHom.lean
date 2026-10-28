import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.MonoidHomParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedMonoidHomEquations

/-! # Intrinsic Monoid Hom -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IntrinsicMonoidHom

noncomputable section

/-! Native bounded homomorphisms map faithfully into test-point data along an isomorphic base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {A B : Over S} {n : ℕ}
variable [IsProper A.hom] [Smooth A.hom] [IsSeparated B.hom] [MonObj A] [MonObj B]
variable (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (P : Polynomial ℚ)

def BoundedNativeMonoidHom :=
  {f : A ⟶ B // IsMonHom f ∧ Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P f}

def boundedNativeMonoidHomToPoint (T : Over S) : BoundedNativeMonoidHom j P → MonoidHomParameters.BoundedFamilyMonoidHom j P T := by
  intro f
  refine ⟨⟨(Over.pullback T.hom).map f.val, ?_⟩, ?_⟩
  · exact Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial.baseChange j P f.property.2 T.hom
  · exact (MappedMonoidHomEquations.mappedMonoidHom_iff (Over.pullback T.hom) f.val).mpr
      ⟨congrArg (Over.pullback T.hom).map f.property.1.one_hom,
        congrArg (Over.pullback T.hom).map f.property.1.mul_hom⟩

omit [AlgebraicGeometry.IsNoetherian S] [IsProper A.hom] in
theorem boundedNativeMonoidHomToPoint_injective (T : Over S) [IsIso T.hom] :
    Function.Injective (boundedNativeMonoidHomToPoint j P T) := by
  intro f q he
  apply Subtype.ext
  exact (Over.pullback T.hom).map_injective
    (congrArg (fun x : MonoidHomParameters.BoundedFamilyMonoidHom j P T => x.val.val) he)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.IntrinsicMonoidHom
