import Mathlib

/-! # Principal Opens -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalOpens.Category

noncomputable section

/-!
# IntegralComparison: the category of principal affine opens

Objects are functions, ordered by inclusion of their principal opens.
Different functions defining the same open are isomorphic objects.
Products are multiplication of functions; the unit function is terminal.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

structure Principal (R : Type u) where
  function : R

variable (R : Type u) [CommRing R]

instance : Preorder (Principal R) where
  le r s := PrimeSpectrum.basicOpen r.function ≤ PrimeSpectrum.basicOpen s.function
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans

def toOpens : Principal R ⥤ TopologicalSpace.Opens (PrimeSpectrum R) :=
  (show Monotone (fun r : Principal R => PrimeSpectrum.basicOpen r.function) from fun _ _ h => h).functor

def top : Principal R := ⟨1⟩

def toTop (r : Principal R) : r ⟶ top R := homOfLE (by
  change PrimeSpectrum.basicOpen r.function ≤ PrimeSpectrum.basicOpen (1 : R)
  rw [PrimeSpectrum.basicOpen_one]
  exact le_top)

def isTerminal : IsTerminal (top R) :=
  IsTerminal.ofUniqueHom (toTop R) (fun _ _ => Subsingleton.elim _ _)

def product (r s : Principal R) : Principal R := ⟨r.function * s.function⟩

def fst (r s : Principal R) : product R r s ⟶ r :=
  homOfLE (PrimeSpectrum.basicOpen_mul_le_left r.function s.function)

def snd (r s : Principal R) : product R r s ⟶ s :=
  homOfLE (PrimeSpectrum.basicOpen_mul_le_right r.function s.function)

def lift {t r s : Principal R} (a : t ⟶ r) (b : t ⟶ s) : t ⟶ product R r s := homOfLE (by
  change PrimeSpectrum.basicOpen t.function ≤ PrimeSpectrum.basicOpen (r.function * s.function)
  rw [PrimeSpectrum.basicOpen_mul]
  exact le_inf (leOfHom a) (leOfHom b))

def fan (r s : Principal R) : BinaryFan r s := BinaryFan.mk (Category.fst R r s) (Category.snd R r s)

def isProduct (r s : Principal R) : IsLimit (fan R r s) :=
  BinaryFan.isLimitMk (fun c => lift R c.fst c.snd)
    (fun _ => Subsingleton.elim _ _) (fun _ => Subsingleton.elim _ _)
    (fun _ _ _ _ => Subsingleton.elim _ _)

instance hasProduct (r s : Principal R) : HasLimit (pair r s) := HasLimit.mk ⟨fan R r s, isProduct R r s⟩

instance hasBinaryProducts : HasBinaryProducts (Principal R) := hasBinaryProducts_of_hasLimit_pair _

instance hasEqualizer {r s : Principal R} (a b : r ⟶ s) : HasEqualizer a b := by
  have he : a = b := Subsingleton.elim _ _
  subst b
  infer_instance

instance hasEqualizers : HasEqualizers (Principal R) := hasEqualizers_of_hasLimit_parallelPair _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalOpens.Category
