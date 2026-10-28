import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CechProduct

/-! # Cech Differential -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CechDifferential.Product

noncomputable section

/-! A graded product rule for the given presheaf differential passes to
the actual Čech cosimplicial modules. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v w t r

variable {R : Type r} [CommRing R] {C : Type u} [Category.{v} C]
  (N : SimplicialObject (FormalCoproduct.{w} C))
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max w t} R) ℕ)

def presheafDifferential (p : ℕ) : CechProduct.cochains N P p ⟶ CechProduct.cochains N P (p + 1) :=
  (FormalCoproduct.cosimplicialObjectFunctor N).map (P.d p (p + 1))

theorem projection_presheafDifferential (p : ℕ) (n : SimplexCategory) (i : (N.obj (op n)).I)
    (x : (CechProduct.cochains N P p).obj n) :
    Cech.BilinearPairing.projection N (P.X (p + 1)) n i ((presheafDifferential N P p).app n x) =
      (P.d p (p + 1)).app (op ((N.obj (op n)).obj i)) (Cech.BilinearPairing.projection N (P.X p) n i x) :=
  ConcreteCategory.congr_hom (CategoryTheory.Limits.Pi.map_π
    (fun j => (P.d p (p + 1)).app (op ((N.obj (op n)).obj j))) i) x

def formDegreeCast {p q : ℕ} (h : p = q) (n : SimplexCategory) :
    (CechProduct.cochains N P p).obj n ≃ₗ[R] (CechProduct.cochains N P q).obj n :=
  h ▸ LinearEquiv.refl R ((CechProduct.cochains N P p).obj n)

theorem projection_formDegreeCast {p q : ℕ} (h : p = q) (n : SimplexCategory)
    (i : (N.obj (op n)).I) (x : (CechProduct.cochains N P p).obj n) :
    Cech.BilinearPairing.projection N (P.X q) n i (formDegreeCast N P h n x) =
      CechProduct.sectionDegreeCast P h (op ((N.obj (op n)).obj i)) (Cech.BilinearPairing.projection N (P.X p) n i x) := by
  subst q
  rfl

variable (μ : ∀ p q (U : Cᵒᵖ), (P.X p).obj U →ₗ[R]
  (P.X q).obj U →ₗ[R] (P.X (p + q)).obj U)

theorem native_projection_pairing (p q : ℕ) (n : SimplexCategory)
    (i : (N.obj (op n)).I) (x : (CechProduct.cochains N P p).obj n) (y : (CechProduct.cochains N P q).obj n) :
    Cech.BilinearPairing.projection N (P.X (p + q)) n i (CechProduct.pairing N P μ p q n x y) =
      μ p q (op ((N.obj (op n)).obj i)) (Cech.BilinearPairing.projection N (P.X p) n i x)
        (Cech.BilinearPairing.projection N (P.X q) n i y) :=
  Cech.BilinearPairing.projection_pairing N _ _ _ (μ p q) n i x y

theorem native_projection_cast_pairing (p q t : ℕ) (h : p + q = t) (n : SimplexCategory)
    (i : (N.obj (op n)).I) (x : (CechProduct.cochains N P p).obj n) (y : (CechProduct.cochains N P q).obj n) :
    Cech.BilinearPairing.projection N (P.X t) n i (formDegreeCast N P h n (CechProduct.pairing N P μ p q n x y)) =
      CechProduct.sectionDegreeCast P h (op ((N.obj (op n)).obj i))
        (μ p q (op ((N.obj (op n)).obj i)) (Cech.BilinearPairing.projection N (P.X p) n i x)
          (Cech.BilinearPairing.projection N (P.X q) n i y)) :=
  (projection_formDegreeCast N P h n i _).trans
    (congrArg (CechProduct.sectionDegreeCast P h (op ((N.obj (op n)).obj i)))
      (native_projection_pairing N P μ p q n i x y))

variable (dμ : ∀ p q (U : Cᵒᵖ) (x : (P.X p).obj U) (y : (P.X q).obj U),
  (P.d (p + q) (p + q + 1)).app U (μ p q U x y) =
    CechProduct.sectionDegreeCast P (by omega : (p + 1) + q = p + q + 1) U
      (μ (p + 1) q U ((P.d p (p + 1)).app U x) y) +
    (-1 : ℤ) ^ p • CechProduct.sectionDegreeCast P (by omega : p + (q + 1) = p + q + 1) U
      (μ p (q + 1) U x ((P.d q (q + 1)).app U y)))

include dμ in
theorem presheafDifferential_pairing (p q : ℕ) (n : SimplexCategory)
    (x : (CechProduct.cochains N P p).obj n) (y : (CechProduct.cochains N P q).obj n) :
    (presheafDifferential N P (p + q)).app n (CechProduct.pairing N P μ p q n x y) =
      formDegreeCast N P (by omega : (p + 1) + q = p + q + 1) n
        (CechProduct.pairing N P μ (p + 1) q n ((presheafDifferential N P p).app n x) y) +
      (-1 : ℤ) ^ p • formDegreeCast N P (by omega : p + (q + 1) = p + q + 1) n
        (CechProduct.pairing N P μ p (q + 1) n x ((presheafDifferential N P q).app n y)) := by
  apply Module.ProductScalarKernel.element_ext
    (fun i => (P.X (p + q + 1)).obj (op ((N.obj (op n)).obj i)))
  intro i
  change Cech.BilinearPairing.projection N (P.X (p + q + 1)) n i _ = Cech.BilinearPairing.projection N (P.X (p + q + 1)) n i _
  let U := op ((N.obj (op n)).obj i)
  let px := Cech.BilinearPairing.projection N (P.X p) n i x
  let py := Cech.BilinearPairing.projection N (P.X q) n i y
  let pr := Cech.BilinearPairing.projection N (P.X (p + q + 1)) n i
  let dx := (presheafDifferential N P p).app n x
  let dy := (presheafDifferential N P q).app n y
  let l := formDegreeCast N P (by omega : (p + 1) + q = p + q + 1) n
    (CechProduct.pairing N P μ (p + 1) q n dx y)
  let r := formDegreeCast N P (by omega : p + (q + 1) = p + q + 1) n
    (CechProduct.pairing N P μ p (q + 1) n x dy)
  have hl : pr l = CechProduct.sectionDegreeCast P (by omega) U
      (μ (p + 1) q U ((P.d p (p + 1)).app U px) py) :=
    (native_projection_cast_pairing N P μ (p + 1) q (p + q + 1) (by omega) n i dx y).trans
      (congrArg (fun z => CechProduct.sectionDegreeCast P (by omega) U (μ (p + 1) q U z py))
        (projection_presheafDifferential N P p n i x))
  have hr : pr r = CechProduct.sectionDegreeCast P (by omega) U
      (μ p (q + 1) U px ((P.d q (q + 1)).app U py)) :=
    (native_projection_cast_pairing N P μ p (q + 1) (p + q + 1) (by omega) n i x dy).trans
      (congrArg (fun z => CechProduct.sectionDegreeCast P (by omega) U (μ p (q + 1) U px z))
        (projection_presheafDifferential N P q n i y))
  have hleft := (projection_presheafDifferential N P (p + q) n i (CechProduct.pairing N P μ p q n x y)).trans
    (congrArg ((P.d (p + q) (p + q + 1)).app U)
      (native_projection_pairing N P μ p q n i x y))
  have hsum : pr (l + (-1 : ℤ) ^ p • r) = pr l + (-1 : ℤ) ^ p • pr r :=
    (pr.map_add l _).trans (congrArg (pr l + ·) (map_zsmul pr ((-1 : ℤ) ^ p) r))
  exact hleft.trans ((dμ p q U px py).trans
    ((congrArg₂ (fun (a b : (P.X (p + q + 1)).obj U) => a + (-1 : ℤ) ^ p • b)
      hl hr).symm.trans hsum.symm))

include dμ in
theorem presheafDifferential_cup (p q a b : ℕ)
    (x : (CechProduct.cochains N P p).obj ⦋a⦌) (y : (CechProduct.cochains N P q).obj ⦋b⦌) :
    (presheafDifferential N P (p + q)).app ⦋a + b⦌ (CechProduct.cup N P μ p q a b x y) =
      formDegreeCast N P (by omega : (p + 1) + q = p + q + 1) ⦋a + b⦌
        (CechProduct.cup N P μ (p + 1) q a b ((presheafDifferential N P p).app ⦋a⦌ x) y) +
      (-1 : ℤ) ^ p • formDegreeCast N P (by omega : p + (q + 1) = p + q + 1) ⦋a + b⦌
        (CechProduct.cup N P μ p (q + 1) a b x ((presheafDifferential N P q).app ⦋b⦌ y)) := by
  have hf := ConcreteCategory.congr_hom
    ((presheafDifferential N P p).naturality (AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion a b)) x
  have hb := ConcreteCategory.congr_hom
    ((presheafDifferential N P q).naturality (AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion a b)) y
  change (presheafDifferential N P (p + q)).app ⦋a + b⦌
    (CechProduct.pairing N P μ p q ⦋a + b⦌ ((CechProduct.cochains N P p).map (AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion a b) x)
      ((CechProduct.cochains N P q).map (AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion a b) y)) = _
  rw [presheafDifferential_pairing N P μ dμ]
  change (presheafDifferential N P p).app ⦋a + b⦌
    ((CechProduct.cochains N P p).map (AlgebraicTopology.Products.SimplexFaceIdentities.frontInclusion a b) x) = _ at hf
  change (presheafDifferential N P q).app ⦋a + b⦌
    ((CechProduct.cochains N P q).map (AlgebraicTopology.Products.SimplexFaceIdentities.backInclusion a b) y) = _ at hb
  rw [hf, hb]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CechDifferential.Product
