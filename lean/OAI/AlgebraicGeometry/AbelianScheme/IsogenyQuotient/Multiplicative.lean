import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterGroupSheaf
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Etale
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Groups
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.RingTheory.Smooth.Basic

/-! # Multiplicative -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Multiplicative.Construction

noncomputable section

/-!
The actual Hopf-algebra model of G_m is smooth and separated. Its native
n-torsion kernel is etale when n is invertible on the base, giving the
geometric target needed for the relative annihilator construction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterGroupSheaf.Construction

def multiplicativeCoordinateLaurentEquiv (R : Type u) [CommRing R] :
    CartierDuality.Characters.Construction.MultiplicativeGroupCoordinate R ≃ₐ[R] LaurentPolynomial R :=
  (MonoidAlgebra.toAdditiveAlgEquiv R R (Multiplicative ℤ)).trans
    (AddMonoidAlgebra.domCongr R R (AddEquiv.additiveMultiplicative ℤ))

theorem multiplicativeCoordinate_smooth (R : Type u) [CommRing R] :
    Algebra.Smooth R (CartierDuality.Characters.Construction.MultiplicativeGroupCoordinate R) := by
  let : IsScalarTower R (Polynomial R) (LaurentPolynomial R) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change LaurentPolynomial.C r = Polynomial.toLaurent (Polynomial.C r)
      exact (Polynomial.toLaurent_C r).symm
  let : Algebra.Smooth (Polynomial R) (LaurentPolynomial R) :=
    Algebra.Smooth.of_isLocalization_Away (Polynomial.X : Polynomial R)
  let : Algebra.Smooth R (Polynomial R) := ⟨inferInstance, inferInstance⟩
  let : Algebra.Smooth R (LaurentPolynomial R) :=
    Algebra.Smooth.comp R (Polynomial R) (LaurentPolynomial R)
  exact Algebra.Smooth.of_equiv (multiplicativeCoordinateLaurentEquiv R).symm

theorem multiplicativeGroupScheme_smooth (R : Type u) [CommRing R] :
    Smooth (CartierDuality.Characters.Construction.multiplicativeGroupScheme R).X.hom := by
  let : Algebra.Smooth R (CartierDuality.Characters.Construction.MultiplicativeGroupCoordinate R) := multiplicativeCoordinate_smooth R
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (CartierDuality.Characters.Construction.MultiplicativeGroupCoordinate R))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr inferInstance

theorem multiplicativeGroupScheme_separated (R : Type u) [CommRing R] :
    IsSeparated (CartierDuality.Characters.Construction.multiplicativeGroupScheme R).X.hom := by
  change IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap R (CartierDuality.Characters.Construction.MultiplicativeGroupCoordinate R))))
  infer_instance

theorem multiplicativeGroupOver_smooth (S : Scheme.{u}) :
    Smooth (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X.hom := by
  let : Smooth (CartierDuality.Characters.Construction.multiplicativeGroupScheme (ULift.{u} ℤ)).X.hom :=
    multiplicativeGroupScheme_smooth _
  change Smooth (Limits.pullback.snd (CartierDuality.Characters.Construction.multiplicativeGroupScheme (ULift.{u} ℤ)).X.hom
    (specULiftZIsTerminal.from S))
  infer_instance

theorem multiplicativeGroupOver_separated (S : Scheme.{u}) :
    IsSeparated (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X.hom := by
  let : IsSeparated (CartierDuality.Characters.Construction.multiplicativeGroupScheme (ULift.{u} ℤ)).X.hom :=
    multiplicativeGroupScheme_separated _
  change IsSeparated (Limits.pullback.snd (CartierDuality.Characters.Construction.multiplicativeGroupScheme (ULift.{u} ℤ)).X.hom
    (specULiftZIsTerminal.from S))
  infer_instance

abbrev rootsOfUnityScheme (S : Scheme.{u}) (n : ℕ) : Over S :=
  Torsion.Groups.Construction.nativeTorsionScheme (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X n

theorem rootsOfUnityScheme_etale (S : Scheme.{u}) (n : ℕ)
    (hn : ∀ x : S, IsUnit (n : S.presheaf.stalk x)) :
    Etale (rootsOfUnityScheme S n).hom := by
  let G := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X
  let : Smooth G.hom := multiplicativeGroupOver_smooth S
  let : Etale (TorsionQuotient.SubgroupFunctor.torsionScheme G n).hom := TorsionQuotient.Etale.TorsionEtale.torsion_etale G n hn
  let e := Torsion.Groups.Construction.torsionEqualizerKernelIso G n
  have : IsIso e.inv.left := (Over.forget S).map_isIso e.inv
  have he : e.inv.left ≫ (TorsionQuotient.SubgroupFunctor.torsionScheme G n).hom = (rootsOfUnityScheme S n).hom := Over.w e.inv
  rw [← he]
  infer_instance

theorem rootsOfUnityScheme_separated (S : Scheme.{u}) (n : ℕ) :
    IsSeparated (rootsOfUnityScheme S n).hom := by
  let G := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X
  let : IsSeparated G.hom := multiplicativeGroupOver_separated S
  let : IsClosedImmersion (TorsionQuotient.SubgroupFunctor.torsionι G n).left := TorsionQuotient.Quasi.TorsionGeometry.torsion_closedImmersion G n
  let : IsSeparated (TorsionQuotient.SubgroupFunctor.torsionScheme G n).hom := by
    have hh : (TorsionQuotient.SubgroupFunctor.torsionι G n).left ≫ G.hom = (TorsionQuotient.SubgroupFunctor.torsionScheme G n).hom := Over.w _
    rw [← hh]
    infer_instance
  let e := Torsion.Groups.Construction.torsionEqualizerKernelIso G n
  have he : e.inv.left ≫ (TorsionQuotient.SubgroupFunctor.torsionScheme G n).hom = (rootsOfUnityScheme S n).hom := Over.w e.inv
  rw [← he]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Multiplicative.Construction
