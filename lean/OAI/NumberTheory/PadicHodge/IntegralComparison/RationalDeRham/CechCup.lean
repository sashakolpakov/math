import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BilinearPairing
import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.WedgeNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent

/-! # Cech Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.CechCup

noncomputable section

/-! Exterior products on the original algebraic form presheaves and
their actual Čech cosimplicial modules. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped Simplicial

universe u

variable (R : Type u) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R)))

local instance rationalSections (U : X.left.Opens) : Algebra ℚ Γ(X.left, U) :=
  Algebra.compHom Γ(X.left, U) (algebraMap ℚ R)

def sectionPairing (p q : ℕ) (U : X.left.Opensᵒᵖ) :
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X p).obj U →ₗ[R]
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X q).obj U →ₗ[R]
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X (p + q)).obj U :=
  (Wedge.wedge R Γ(X.left, U.unop) p q).restrictScalars₁₂ R R

theorem sectionPairing_natural (p q : ℕ) {U V : X.left.Opensᵒᵖ} (f : U ⟶ V)
    (x : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X p).obj U)
    (y : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X q).obj U) :
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X (p + q)).map f (sectionPairing R X p q U x y) =
      sectionPairing R X p q V ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X p).map f x)
        ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X q).map f y) := by
  let : Algebra ℚ ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj U) := rationalSections R X U.unop
  let : Algebra ℚ ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj V) := rationalSections R X V.unop
  exact WedgeNaturality.formMap_wedge ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map f) p q x y

variable (N : SimplicialObject (FormalCoproduct.{u} X.left.Opens))

def cochains (p : ℕ) : CosimplicialObject (ModuleCat.{u} R) :=
  Cech.BilinearPairing.cosimplicial N (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X p)

def pairing (p q : ℕ) (n : SimplexCategory) :
    (cochains R X N p).obj n →ₗ[R] (cochains R X N q).obj n →ₗ[R]
      (cochains R X N (p + q)).obj n :=
  Cech.BilinearPairing.pairing N
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X p) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X q)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X (p + q)) (sectionPairing R X p q) n

theorem pairing_natural (p q : ℕ) {n m : SimplexCategory} (f : n ⟶ m)
    (x : (cochains R X N p).obj n) (y : (cochains R X N q).obj n) :
    (cochains R X N (p + q)).map f (pairing R X N p q n x y) =
      pairing R X N p q m ((cochains R X N p).map f x) ((cochains R X N q).map f y) :=
  Cech.BilinearPairing.pairing_natural N _ _ _ (sectionPairing R X p q)
    (sectionPairing_natural R X p q) f x y

def cup (p q a b : ℕ) :
    (cochains R X N p).obj ⦋a⦌ →ₗ[R] (cochains R X N q).obj ⦋b⦌ →ₗ[R]
      (cochains R X N (p + q)).obj ⦋a + b⦌ :=
  Cosimplicial.BilinearCup.cup (cochains R X N p) (cochains R X N q)
    (cochains R X N (p + q)) (pairing R X N p q) a b

theorem differential_cup (p q a b : ℕ)
    (x : (cochains R X N p).obj ⦋a⦌) (y : (cochains R X N q).obj ⦋b⦌) :
    Cosimplicial.BilinearCup.differential (cochains R X N (p + q)) (a + b)
        (cup R X N p q a b x y) =
      pairing R X N p q ⦋a + b + 1⦌
        ((cochains R X N p).map
          (SimplexCategory.subinterval 0 (a + 1) (by omega : 0 + (a + 1) ≤ a + b + 1))
          (Cosimplicial.BilinearCup.differential (cochains R X N p) a x))
        ((cochains R X N q).map
          (SimplexCategory.subinterval (a + 1) b (by omega : (a + 1) + b ≤ a + b + 1)) y) +
      (-1 : ℤ) ^ a • pairing R X N p q ⦋a + b + 1⦌
        ((cochains R X N p).map
          (SimplexCategory.subinterval 0 a (by omega : 0 + a ≤ a + b + 1)) x)
        ((cochains R X N q).map
          (SimplexCategory.subinterval a (b + 1) (by omega : a + (b + 1) ≤ a + b + 1))
          (Cosimplicial.BilinearCup.differential (cochains R X N q) b y)) :=
  Cosimplicial.BilinearCup.differential_cup _ _ _ (pairing R X N p q)
    (pairing_natural R X N p q) a b x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.CechCup
