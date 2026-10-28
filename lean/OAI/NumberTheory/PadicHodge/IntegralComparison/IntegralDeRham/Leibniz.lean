import OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.WedgeSigns

/-! # Leibniz -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.Leibniz.Wedge

noncomputable section

/-! The actual exterior differential satisfies graded Leibniz for the
integral symbol wedge, including in positive characteristic. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

theorem differential_wedge_symbols (p q : ℕ) (a b : A) (v : Fin p → A) (w : Fin q → A) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A (p + q) (DeRhamWedge.wedge R A p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w)) =
      WedgeSigns.degreeCast R A (by omega : (p + 1) + q = p + q + 1)
        (DeRhamWedge.wedge R A (p + 1) q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A p (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w)) +
      (-1 : ℤ) ^ p • WedgeSigns.degreeCast R A (by omega : p + (q + 1) = p + q + 1)
        (DeRhamWedge.wedge R A p (q + 1) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w))) := by
  simp only [DeRhamWedge.wedge_symbol, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential_symbol, mul_one, one_mul]
  rw [WedgeSigns.degreeCast_append_cons]
  change AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 (Fin.cons (a * b) (Fin.append v w)) =
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b (Fin.cons a (Fin.append v w)) +
      (-1 : ℤ) ^ p • AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a (Fin.append v (Fin.cons b w))
  rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_cons_mul, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one R A b, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one R A a, WedgeSigns.symbol_append_cons]
  have hsign : (-1 : ℤ) ^ p * (-1 : ℤ) ^ p = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow (show Even (p + p) from ⟨p, rfl⟩)
  have hs (z : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A (p + q + 1)) :
      (-1 : ℤ) ^ p • (a • ((-1 : ℤ) ^ p • z)) = a • z := by
    rw [smul_comm ((-1 : ℤ) ^ p) a, smul_smul, hsign, one_smul]
  rw [hs]
  exact add_comm _ _

theorem differential_wedge (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A (p + q) (DeRhamWedge.wedge R A p q x y) =
      WedgeSigns.degreeCast R A (by omega : (p + 1) + q = p + q + 1)
        (DeRhamWedge.wedge R A (p + 1) q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A p x) y) +
      (-1 : ℤ) ^ p • WedgeSigns.degreeCast R A (by omega : p + (q + 1) = p + q + 1)
        (DeRhamWedge.wedge R A p (q + 1) x (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A q y)) := by
  let L : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A (p + q + 1) :=
    ((DeRhamWedge.wedge R A p q).restrictScalars₁₂ R R).compr₂ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A (p + q))
  let DL : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A (p + q + 1) :=
    (((DeRhamWedge.wedge R A (p + 1) q).restrictScalars₁₂ R R).compl₁₂
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A p) LinearMap.id).compr₂
        ((WedgeSigns.degreeCast R A (by omega : (p + 1) + q = p + q + 1)).toLinearMap.restrictScalars R)
  let DR : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A (p + q + 1) :=
    (((DeRhamWedge.wedge R A p (q + 1)).restrictScalars₁₂ R R).compl₁₂
      LinearMap.id (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A q)).compr₂
        ((WedgeSigns.degreeCast R A (by omega : p + (q + 1) = p + q + 1)).toLinearMap.restrictScalars R)
  have h : L = DL + (-1 : ℤ) ^ p • DR := by
    apply RationalDeRham.Leibniz.Wedge.linearMap_ext_symbols R A p
    intro a v
    apply RationalDeRham.Leibniz.Wedge.linearMap_ext_symbols R A q
    intro b w
    exact differential_wedge_symbols R A p q a b v w
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.Leibniz.Wedge
