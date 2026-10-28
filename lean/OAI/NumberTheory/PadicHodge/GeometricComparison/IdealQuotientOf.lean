import OAI.NumberTheory.PadicHodge.GeometricComparison.IdealQuotientEq
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotientTransition

/-! # Ideal Quotient Of -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IdealQuotientOf.IdealQuotientRestrictionLevel

noncomputable section

/-! Scalar restriction of coefficient quotients respects transitions
between the actual ideals, including specified extended-ideal coordinates. -/

open _root_.CategoryTheory

universe u v w
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  (I J : Ideal R) (hIJ : I ≤ J)

local notation "G" => ModuleCat.restrictScalars (algebraMap R S)

theorem natural : (IdealQuotientEq.IdealQuotientRestriction.iso.{u, v, w} R S I).hom ≫
    Functor.whiskerRight (IntegralComparison.Module.IdealQuotientTransition.transformation S
      (I.map (algebraMap R S)) (J.map (algebraMap R S)) (Ideal.map_mono hIJ)) G =
    Functor.whiskerLeft G (IntegralComparison.Module.IdealQuotientTransition.transformation R I J hIJ) ≫
      (IdealQuotientEq.IdealQuotientRestriction.iso R S J).hom := by
  apply NatTrans.ext
  funext M
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (I • (⊤ : Submodule R ((G).obj M))).mkQ_surjective x
  rfl

def isoOfEq (K : Ideal S) (hK : I.map (algebraMap R S) = K) :
    G ⋙ IntegralComparison.Module.IdealQuotient.functor.{u, w} R I ≅ IntegralComparison.Module.IdealQuotient.functor S K ⋙ G :=
  hK ▸ IdealQuotientEq.IdealQuotientRestriction.iso R S I

theorem naturalOfEq (K L : Ideal S) (hK : I.map (algebraMap R S) = K)
    (hL : J.map (algebraMap R S) = L) (hKL : K ≤ L) :
    (isoOfEq.{u, v, w} R S I K hK).hom ≫
      Functor.whiskerRight (IntegralComparison.Module.IdealQuotientTransition.transformation S K L hKL) G =
    Functor.whiskerLeft G (IntegralComparison.Module.IdealQuotientTransition.transformation R I J hIJ) ≫
      (isoOfEq R S J L hL).hom := by
  subst K L
  exact natural R S I J hIJ

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IdealQuotientOf.IdealQuotientRestrictionLevel
