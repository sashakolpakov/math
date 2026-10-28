import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PointedFieldPullbackDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.PullbackMapEquality

/-! # Bounded Pointed Map Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.BoundedPointedMapDetection

noncomputable section

/-! Native bounded identity-preserving maps of abelian schemes are determined by all field-valued pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem nativeBoundedPointedMap_eq_of_fieldPullbacks
    {S : Scheme.{u}} [IsNoetherian S] {g h n : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
    [IsClosedImmersion j.left] (P : Polynomial ℚ) (f q : A.scheme ⟶ B.scheme)
    (hf : η[A.scheme] ≫ f = η[B.scheme]) (hq : η[A.scheme] ≫ q = η[B.scheme])
    (hpf : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P f) (hpq : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P q)
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ S),
      (Over.pullback s).map f = (Over.pullback s).map q) : f = q := by
  let T : Over S := Over.mk (𝟙 S)
  let F := Over.pullback (𝟙 S)
  let f' : Bounded.PointedMapParameters.BoundedFamilyPointedMap j P T := ⟨⟨F.map f, hpf.baseChange j P (𝟙 S)⟩,
    (MappedMonoidHomEquations.mappedMonoidHom_one_iff F f).mpr (congrArg F.map hf)⟩
  let q' : Bounded.PointedMapParameters.BoundedFamilyPointedMap j P T := ⟨⟨F.map q, hpq.baseChange j P (𝟙 S)⟩,
    (MappedMonoidHomEquations.mappedMonoidHom_one_iff F q).mpr (congrArg F.map hq)⟩
  have H : f' = q' := by
    apply Bounded.PointedFieldPullbackDetection.boundedPointedMap_eq_of_fieldPullbacks A B j P
    intro K _ s
    change (Over.pullback s).map (F.map f) = (Over.pullback s).map (F.map q)
    exact (Iterated.PullbackMapEquality.overPullback_map_eq_iff_iterated s (𝟙 S) f q).mp (h K (s ≫ 𝟙 S))
  exact F.map_injective (congrArg (fun D : Bounded.PointedMapParameters.BoundedFamilyPointedMap j P T => D.val.val) H)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.BoundedPointedMapDetection
