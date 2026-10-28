import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.ProductLocalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.LocalizedFixedClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechCoordinates

/-! # Localization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.Localization

noncomputable section

/-! Localization on a finite augmented ordered Čech complex kills
only classes annihilated by a power of the localization parameter.
Consequently it detects classes fixed by that parameter. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechCoordinates
variable {R : Type u} [CommRing R] {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → C)
  {P Q : Cᵒᵖ ⥤ ModuleCat.{u} R} (α : P ⟶ Q) (z : R)
  (hsurj : ∀ j (y : Q.obj j), ∃ (a : ℕ) (x : P.obj j), z^a • y = α.app j x)
  (hker : ∀ j (x : P.obj j), α.app j x = 0 → ∃ a : ℕ, z^a • x = 0)

include hsurj in
theorem degree_surj (q : ℕ) (y : (AugmentedOrdered.Cech.complex U Q).X q) :
    ∃ (a : ℕ) (x : (AugmentedOrdered.Cech.complex U P).X q), z^a • y = (AugmentedOrdered.CechFunctor.complexMap U α).f q x := by
  have : Finite (AugmentedOrdered.Cech.Index ι q) := inferInstanceAs (Finite {a : Fin q → ι // StrictMono a})
  exact IntegralComparison.Finite.ProductLocalization.surj z
    (fun a : AugmentedOrdered.Cech.Index ι q => P.obj (op ((AugmentedOrdered.Cech.formal U q).obj a)))
    (fun a : AugmentedOrdered.Cech.Index ι q => Q.obj (op ((AugmentedOrdered.Cech.formal U q).obj a)))
    (fun a => α.app (op ((AugmentedOrdered.Cech.formal U q).obj a)))
    (fun a => hsurj (op ((AugmentedOrdered.Cech.formal U q).obj a))) y

include hker in
theorem degree_kernel (q : ℕ) (x : (AugmentedOrdered.Cech.complex U P).X q)
    (hx : (AugmentedOrdered.CechFunctor.complexMap U α).f q x = 0) : ∃ a : ℕ, z^a • x = 0 := by
  have : Finite (AugmentedOrdered.Cech.Index ι q) := inferInstanceAs (Finite {a : Fin q → ι // StrictMono a})
  exact IntegralComparison.Finite.ProductLocalization.kernel z
    (fun a : AugmentedOrdered.Cech.Index ι q => P.obj (op ((AugmentedOrdered.Cech.formal U q).obj a)))
    (fun a : AugmentedOrdered.Cech.Index ι q => Q.obj (op ((AugmentedOrdered.Cech.formal U q).obj a)))
    (fun a => α.app (op ((AugmentedOrdered.Cech.formal U q).obj a)))
    (fun a => hker (op ((AugmentedOrdered.Cech.formal U q).obj a))) x hx

include hsurj hker in
theorem homology_kernel (n : ℕ) (x : (AugmentedOrdered.Cech.complex U P).homology n)
    (hx : homologyMap (AugmentedOrdered.CechFunctor.complexMap U α) n x = 0) : ∃ a : ℕ, z^a • x = 0 :=
  Cochain.LocalizedFixedClass.homology_kernel z (AugmentedOrdered.CechFunctor.complexMap U α)
    (degree_surj U α z hsurj) (degree_kernel U α z hker) n x hx

include hsurj hker in
theorem eq_of_map_eq (n : ℕ) (x y : (AugmentedOrdered.Cech.complex U P).homology n)
    (hx : z • x = x) (hy : z • y = y)
    (h : homologyMap (AugmentedOrdered.CechFunctor.complexMap U α) n x = homologyMap (AugmentedOrdered.CechFunctor.complexMap U α) n y) : x = y :=
  Cochain.LocalizedFixedClass.eq_of_map_eq z (AugmentedOrdered.CechFunctor.complexMap U α)
    (degree_surj U α z hsurj) (degree_kernel U α z hker) n x y hx hy h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.Localization
