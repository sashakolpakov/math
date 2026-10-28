import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Prime Power Id -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PrimePowerId.PrimePowerAlgebraQuotient

noncomputable section

/-! The canonical prime-power quotient functor and its reduction transformation. -/

open _root_.CategoryTheory

universe u v
variable (R : Type u) [CommRing R] (p n : ℕ)

def ideal (A : CommAlgCat.{v} R) : Ideal A := (Ideal.span {(p : A)}) ^ (n + 1)

theorem ideal_map {A B : CommAlgCat.{v} R} (f : A ⟶ B) :
    (ideal R p n A).map f.hom.toRingHom = ideal R p n B := by
  simp only [ideal, Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast]

def object (A : CommAlgCat.{v} R) : CommAlgCat.{v} R := CommAlgCat.of R (A ⧸ ideal R p n A)

def map {A B : CommAlgCat.{v} R} (f : A ⟶ B) : object R p n A ⟶ object R p n B :=
  CommAlgCat.ofHom (Ideal.quotientMapₐ (ideal R p n B) f.hom
    ((Ideal.map_le_iff_le_comap).mp (ideal_map R p n f).le))

theorem map_mk {A B : CommAlgCat.{v} R} (f : A ⟶ B) (a : A) :
    (PrimePowerAlgebraQuotient.map R p n f).hom (Ideal.Quotient.mk (ideal R p n A) a) =
      Ideal.Quotient.mk (ideal R p n B) (f.hom a) := rfl

theorem map_id (A : CommAlgCat.{v} R) : PrimePowerAlgebraQuotient.map R p n (𝟙 A) = 𝟙 (object R p n A) := by
  ext a
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

theorem map_comp {A B C : CommAlgCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) :
    PrimePowerAlgebraQuotient.map R p n (f ≫ g) = PrimePowerAlgebraQuotient.map R p n f ≫ PrimePowerAlgebraQuotient.map R p n g := by
  ext a
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

def functor : CommAlgCat.{v} R ⥤ CommAlgCat.{v} R where
  obj := object R p n
  map := PrimePowerAlgebraQuotient.map R p n
  map_id := PrimePowerAlgebraQuotient.map_id R p n
  map_comp := PrimePowerAlgebraQuotient.map_comp R p n

def reduction : 𝟭 (CommAlgCat.{v} R) ⟶ functor R p n where
  app A := CommAlgCat.ofHom (Ideal.Quotient.mkₐ R (ideal R p n A))
  naturality A B f := by ext a; rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PrimePowerId.PrimePowerAlgebraQuotient
