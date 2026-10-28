import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TupleRestrictionFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechCoordinates

/-! # Projection -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Projection

noncomputable section

/-! The ordered nonempty Čech complex and its literal projection from
the native all-tuples complex, for arbitrary presheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite

universe u v
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {D : Type v} [Category D] [Preadditive D] [HasProducts.{u} D]
  {ι : Type u} [LinearOrder ι] (U : ι → C) (P : Cᵒᵖ ⥤ D)

abbrev Index (n : ℕ) := {a : Fin (n + 1) → ι // StrictMono a}
abbrev factor {n : ℕ} (a : Fin (n + 1) → ι) :=
  Cech.TupleRestrictionFunctor.factor U P a
abbrev object (n : ℕ) := AugmentedOrdered.Cech.object U P (n + 1)
abbrev differential (n : ℕ) := AugmentedOrdered.Cech.differential U P (n + 1)

def complex : CochainComplex D ℕ := CochainComplex.of (object U P) (differential U P)
  (fun n => AugmentedOrdered.Cech.differential_comp U P (n + 1))

def projection (n : ℕ) (a : Index (ι := ι) n) : object U P n ⟶ factor U P a.val :=
  Pi.π (fun b : Index (ι := ι) n => factor U P b.val) a

def mapF (n : ℕ) : (Cech.TupleRestrictionFunctor.complex U P).X n ⟶ object U P n :=
  Pi.lift fun a : Index (ι := ι) n => Cech.TupleRestrictionFunctor.projection U P a.val

theorem mapF_projection (n : ℕ) (a : Index (ι := ι) n) :
    mapF U P n ≫ projection U P n a = Cech.TupleRestrictionFunctor.projection U P a.val :=
  Pi.lift_comp_π _ a

def zeroExtension (n : ℕ) : object U P n ⟶ (Cech.TupleRestrictionFunctor.complex U P).X n := by
  classical
  exact Pi.lift fun a : Fin (n + 1) → ι => if h : StrictMono a then projection U P n ⟨a, h⟩ else 0

theorem zeroExtension_projection (n : ℕ) (a : Fin (n + 1) → ι) (ha : StrictMono a) :
    zeroExtension U P n ≫ Cech.TupleRestrictionFunctor.projection U P a =
      projection U P n ⟨a, ha⟩ := by
  classical
  change (Pi.lift (fun b : Fin (n + 1) → ι =>
    if h : StrictMono b then projection U P n ⟨b, h⟩ else 0)) ≫
      Pi.π (fun b : Fin (n + 1) → ι => factor U P b) a = _
  rw [Pi.lift_comp_π, dite_eq_left ha]

theorem zeroExtension_mapF (n : ℕ) : zeroExtension U P n ≫ mapF U P n = 𝟙 _ := by
  apply Pi.hom_ext
  intro (a : Index (ι := ι) n)
  change _ ≫ projection U P n a = _ ≫ projection U P n a
  rw [Category.assoc, mapF_projection, zeroExtension_projection U P n a.val a.property,
    Category.id_comp]

instance mapF_epi (n : ℕ) : Epi (mapF U P n) :=
  (IsSplitEpi.mk' ⟨zeroExtension U P n, zeroExtension_mapF U P n⟩).epi

theorem differential_projection (n : ℕ) (a : Index (ι := ι) (n + 1)) :
    differential U P n ≫ projection U P (n + 1) a =
      ∑ k : Fin (n + 2), (-1 : ℤ)^k.val •
        (projection U P n (AugmentedOrdered.Cech.Index.delete a k) ≫
          P.map ((AugmentedOrdered.Cech.face U (n + 1) k).φ a).op) :=
  AugmentedOrdered.CechCoordinates.differential_comp_pi U P (n + 1) a

theorem mapF_d (n : ℕ) :
    mapF U P n ≫ differential U P n =
      (Cech.TupleRestrictionFunctor.complex U P).d n (n + 1) ≫ mapF U P (n + 1) := by
  apply Pi.hom_ext
  intro (a : Index (ι := ι) (n + 1))
  change _ ≫ projection U P (n + 1) a = _ ≫ projection U P (n + 1) a
  erw [Category.assoc, differential_projection, comp_sum, Category.assoc,
    mapF_projection, NonemptyCechDifferential.differential_projection]
  apply Finset.sum_congr rfl
  intro k _
  erw [comp_zsmul, ← Category.assoc, mapF_projection]
  rfl

def map : Cech.TupleRestrictionFunctor.complex U P ⟶ complex U P :=
  CochainComplex.ofHom (mapF U P) fun n => by
    rw [show (complex U P).d n (n + 1) = differential U P n from CochainComplex.of_d _ _ n]
    exact mapF_d U P n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Projection
