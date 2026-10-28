import OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedSerreVanishing
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechVanishingTransfer

/-! # Twist Vanishing -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.TwistVanishing

noncomputable section

/-! Serre vanishing for actual Ext-based sheaf cohomology on a closed
projective scheme over any noetherian coefficient ring. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace MonoidalCategory

open OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechVanishingTransfer
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
local instance (X : Scheme.{u}) : MonoidalCategory X.Modules := SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

theorem projectiveTwist_eventually_vanishing
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    {X : Scheme.{u}} [X.IsSeparated]
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    [IsClosedImmersion i] (j : Fin (n + 1))
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ b : ℕ, ∀ m : ℕ, b ≤ m → ∀ q : ℕ, 0 < q →
      Subsingleton (SheafCohomology.AffineH.Projective.H (M ⊗ (Scheme.Modules.pullback i).obj
        (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)) q) := by
  obtain ⟨b, hb⟩ :=
    SheafCohomology.Projective.ClosedSerreVanishing.MvPolynomial.closedImmersion_finiteType_eventually_orderedBaseCechComplex_exactAt_of_pos i M j
  let U := fun k : ULift.{u} (Fin (n + 1)) =>
    i ⁻¹ᵁ SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) k
  have hU : IsOpenCover U :=
    (IsOpenCover.mk (SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top
      (R := R) (σ := Fin (n + 1)))).comap i.base.hom
  have hUa (k : ULift.{u} (Fin (n + 1))) : IsAffineOpen (U k) :=
    (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R) k).preimage i
  refine ⟨b, fun m hm q hq => ?_⟩
  let T := M ⊗ (Scheme.Modules.pullback i).obj
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)
  have : T.IsQuasicoherent :=
    ((SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower_isInvertible (R := R) j m).pullback i).tensorObj_isQuasicoherent
  exact SheafCohomology.Projective.BaseCechVanishingTransfer.orderedBaseCech_exactAt_subsingleton_H
    (i ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 1)))
    T U hU hUa q (hb m hm q hq)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.TwistVanishing
