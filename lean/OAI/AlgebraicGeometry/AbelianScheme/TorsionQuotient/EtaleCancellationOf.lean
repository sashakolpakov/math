import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SmoothLocal
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeFiniteness
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Etale Cancellation Of -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.EtaleCancellationOf.EtaleCancellation

/-! Étaleness descends through a finite locally free surjective source map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem algebra_unramified
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B] [Algebra.FormallyEtale A B]
    [Algebra.FormallyUnramified R B] : Algebra.FormallyUnramified R A := by
  constructor
  have : Subsingleton (TensorProduct A B (KaehlerDifferential R A)) :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B).subsingleton
  exact Module.FaithfullyFlat.lTensor_reflects_triviality A B _

theorem formallyUnramified_of_etale_cover
    {X Q S : Scheme.{u}} (q : X ⟶ Q) (b : Q ⟶ S)
    [Etale q] [Surjective q] [FormallyUnramified (q ≫ b)] : FormallyUnramified b := by
  apply HasRingHomProperty.of_stalkMap (P := @FormallyUnramified.{u})
    RingHom.FormallyUnramified.ofLocalizationPrime
  intro y
  obtain ⟨x, rfl⟩ := q.surjective y
  let R := S.presheaf.stalk (b (q x))
  let A := Q.presheaf.stalk (q x)
  let B := X.presheaf.stalk x
  let : Algebra R A := (b.stalkMap (q x)).hom.toAlgebra
  let : Algebra A B := (q.stalkMap x).hom.toAlgebra
  let : Algebra R B := ((q.stalkMap x).hom.comp (b.stalkMap (q x)).hom).toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FormallyUnramified A B := FormallyUnramified.stalkMap q x
  have : Algebra.FormallySmooth A B := SmoothLocal.SmoothLocalLifting.formallySmooth_stalk q x
  have : Algebra.FormallyEtale A B :=
    Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth
  have : Module.FaithfullyFlat A B :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap q x) (q.toLRSHom.prop x)
  have hcomp := FormallyUnramified.stalkMap (q ≫ b) x
  rw [Scheme.Hom.stalkMap_comp] at hcomp
  have : Algebra.FormallyUnramified R B := hcomp
  exact algebra_unramified R A B

theorem etale_of_finite_flat_cover
    {X Q S : Scheme.{u}} (q : X ⟶ Q) (b : Q ⟶ S)
    [IsFinite q] [Flat q] [LocallyOfFinitePresentation q] [Surjective q]
    [Etale (q ≫ b)] : Etale b := by
  have : FormallyUnramified q := FormallyUnramified.of_comp q b
  have : Etale q := Etale.of_formallyUnramified_of_flat q
  have : FormallyUnramified b := formallyUnramified_of_etale_cover q b
  have : Flat b := Quotients.FiniteDescent.SchemeFiniteness.Construction.SchemeFinitenessDescent.flat q b
  have : LocallyOfFinitePresentation b :=
    Quotients.FiniteDescent.SchemeFiniteness.Construction.SchemeFinitenessDescent.locallyOfFinitePresentation q b
  exact Etale.of_formallyUnramified_of_flat b

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.EtaleCancellationOf.EtaleCancellation
