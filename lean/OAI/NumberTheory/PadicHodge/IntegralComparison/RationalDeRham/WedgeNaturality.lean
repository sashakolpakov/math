import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.WedgeAlgebra

/-! # Wedge Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.WedgeNaturality

noncomputable section

/-! The original algebraic pullback maps on differential symbols
preserve the native wedge product and its unit. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable {R : Type u} [CommRing R] {A B : CommAlgCat.{u} R}
  [Algebra ℚ A] [Algebra ℚ B]

theorem formMap_wedge (f : A ⟶ B) (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f (p + q) (Wedge.wedge R A p q x y) =
      Wedge.wedge R B p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f p x) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f q y) := by
  let L : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B (p + q) :=
    ((Wedge.wedge R A p q).restrictScalars₁₂ R R).compr₂ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f (p + q))
  let D : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B (p + q) :=
    ((Wedge.wedge R B p q).restrictScalars₁₂ R R).compl₁₂
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f p) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f q)
  have h : L = D := by
    apply Leibniz.Wedge.linearMap_ext_symbols R A p
    intro a v
    apply Leibniz.Wedge.linearMap_ext_symbols R A q
    intro b w
    change AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f (p + q) (Wedge.wedge R A p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w)) =
      Wedge.wedge R B p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f p (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v))
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w))
    rw [Wedge.wedge_symbol, AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol, AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol,
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol, Wedge.wedge_symbol, map_mul]
    congr 1
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

omit [Algebra ℚ A] [Algebra ℚ B] in
theorem formMap_unit (f : A ⟶ B) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f 0 (WedgeAlgebra.unitForm R A) = WedgeAlgebra.unitForm R B := by
  rw [WedgeAlgebra.unitForm, AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol, map_one]
  exact congrArg (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B 1) (Subsingleton.elim _ _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.WedgeNaturality
