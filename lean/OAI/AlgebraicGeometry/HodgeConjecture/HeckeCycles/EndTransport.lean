import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Polynomial

/-! # End Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndTransport.CM

noncomputable section

/-! Genuine algebraic endomorphisms and their Frobenius polynomials
transport through an actual isomorphism of group schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct
open OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction

variable {S : Scheme} (G H : CommGrp (Over S)) (e : G.toGrp ≅ H.toGrp)

def transport : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd G.X ≃+* FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd H.X where
  toFun f := Additive.ofMul (e.inv ≫ f.toMul ≫ e.hom)
  invFun f := Additive.ofMul (e.hom ≫ f.toMul ≫ e.inv)
  left_inv f := by
    apply Additive.toMul.injective
    change e.hom ≫ (e.inv ≫ f.toMul ≫ e.hom) ≫ e.inv = f.toMul
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  right_inv f := by
    apply Additive.toMul.injective
    change e.inv ≫ (e.hom ≫ f.toMul ≫ e.inv) ≫ e.hom = f.toMul
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  map_add' f g := by
    apply Additive.toMul.injective
    change e.inv ≫ (f.toMul * g.toMul) ≫ e.hom =
      (e.inv ≫ f.toMul ≫ e.hom) * (e.inv ≫ g.toMul ≫ e.hom)
    rw [MonObj.mul_comp, MonObj.comp_mul]
  map_mul' f g := by
    apply Additive.toMul.injective
    change e.inv ≫ (g.toMul ≫ f.toMul) ≫ e.hom =
      (e.inv ≫ g.toMul ≫ e.hom) ≫ (e.inv ≫ f.toMul ≫ e.hom)
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

theorem transport_schemeMap (f : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd G.X) :
    (transport G H e f).toMul.hom.hom =
      e.inv.hom.hom ≫ f.toMul.hom.hom ≫ e.hom.hom.hom := rfl

def groupIso (u : G.X ≅ H.X) [IsMonHom u.hom] : G.toGrp ≅ H.toGrp where
  hom := Grp.ofHom u.hom
  inv := Grp.ofHom u.inv
  hom_inv_id := by apply Grp.hom_ext; exact u.hom_inv_id
  inv_hom_id := by apply Grp.hom_ext; exact u.inv_hom_id

def schemeTransport (u : G.X ≅ H.X) [IsMonHom u.hom] :
    FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd G.X ≃+* FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd H.X :=
  transport G H (groupIso G H u)

variable {k : Type} [Field k] [Fintype k]
  (A B : CommGrp (Over (Spec (.of k)))) (g : A.toGrp ≅ B.toGrp)

theorem transport_frobenius :
    transport A B g (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A.X) = FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k B.X := by
  apply Additive.toMul.injective
  apply Grp.hom_ext
  let e : A.X ≅ B.X := (Grp.forget _).mapIso g
  change e.inv ≫ FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius k A.X ≫ e.hom = FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius k B.X
  rw [FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius_naturality, Iso.inv_hom_id_assoc]

theorem transport_frobenius_polynomial (q : ℕ) (T : Fin 3 → FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.X)
    (h : Ordinary.Polynomial.CM.heckePolynomialValue q (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A.X) T = 0) :
    Ordinary.Polynomial.CM.heckePolynomialValue q (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k B.X)
      (fun i => transport A B g (T i)) = 0 := by
  have hmap := congrArg (transport A B g) h
  simpa only [Ordinary.Polynomial.CM.heckePolynomialValue, map_sub, map_add, map_mul,
    map_pow, map_nsmul, map_zero, transport_frobenius] using hmap

theorem schemeTransport_frobenius_polynomial (u : A.X ≅ B.X) [IsMonHom u.hom]
    (q : ℕ) (T : Fin 3 → FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.X)
    (h : Ordinary.Polynomial.CM.heckePolynomialValue q (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A.X) T = 0) :
    Ordinary.Polynomial.CM.heckePolynomialValue q (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k B.X)
      (fun i => schemeTransport A B u (T i)) = 0 :=
  transport_frobenius_polynomial A B (groupIso A B u) q T h

/-- Passing to rational endomorphisms preserves the literal integral
Frobenius polynomial and its coefficients. -/
theorem rational_frobenius_polynomial (q : ℕ) (T : Fin 3 → FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.X)
    (h : Ordinary.Polynomial.CM.heckePolynomialValue q (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A.X) T = 0) :
    Ordinary.Polynomial.CM.heckePolynomialValue q (FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius k A.X)
      (fun i => (1 : ℚ) ⊗ₜ[ℤ] T i) = 0 := by
  let incl : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.X →ₐ[ℤ] FormalGeometry.Completion.Endomorphisms.Construction.RationalAlgebraicEnd A.X :=
    Algebra.TensorProduct.includeRight
  have hmap := congrArg incl h
  simpa only [Ordinary.Polynomial.CM.heckePolynomialValue, map_sub, map_add, map_mul,
    map_pow, map_nsmul, map_zero, incl, Algebra.TensorProduct.includeRight_apply,
    FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius] using hmap

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndTransport.CM
