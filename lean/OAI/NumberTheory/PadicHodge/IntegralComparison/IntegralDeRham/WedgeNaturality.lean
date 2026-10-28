import OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.DeRhamWedge
import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.WedgeNaturality

/-! # Wedge Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.WedgeNaturality

noncomputable section

/-! The integral native wedge commutes with the actual algebra maps
and agrees with the established rational wedge after inversion. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

theorem formMap_wedge {R : Type u} [CommRing R] {A B : CommAlgCat.{u} R}
    (f : A ⟶ B) (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f (p + q) (DeRhamWedge.wedge R A p q x y) =
      DeRhamWedge.wedge R B p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f p x) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f q y) := by
  let L : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B (p + q) :=
    ((DeRhamWedge.wedge R A p q).restrictScalars₁₂ R R).compr₂ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f (p + q))
  let D : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B (p + q) :=
    ((DeRhamWedge.wedge R B p q).restrictScalars₁₂ R R).compl₁₂
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f p) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f q)
  have h : L = D := by
    apply RationalDeRham.Leibniz.Wedge.linearMap_ext_symbols R A p
    intro a v
    apply RationalDeRham.Leibniz.Wedge.linearMap_ext_symbols R A q
    intro b w
    change AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f (p + q) (DeRhamWedge.wedge R A p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w)) =
      DeRhamWedge.wedge R B p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f p (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v))
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w))
    rw [DeRhamWedge.wedge_symbol, AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol, AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol,
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol, DeRhamWedge.wedge_symbol, map_mul]
    congr 1
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

theorem wedge_eq_rational (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra ℚ A] (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q) :
    DeRhamWedge.wedge R A p q x y = RationalDeRham.Wedge.wedge R A p q x y := by
  let L := (DeRhamWedge.wedge R A p q).restrictScalars₁₂ R R
  let D := (RationalDeRham.Wedge.wedge R A p q).restrictScalars₁₂ R R
  have h : L = D := by
    apply RationalDeRham.Leibniz.Wedge.linearMap_ext_symbols R A p
    intro a v
    apply RationalDeRham.Leibniz.Wedge.linearMap_ext_symbols R A q
    intro b w
    change DeRhamWedge.wedge R A p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w) =
      RationalDeRham.Wedge.wedge R A p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w)
    rw [DeRhamWedge.wedge_symbol, RationalDeRham.Wedge.wedge_symbol]
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.WedgeNaturality
