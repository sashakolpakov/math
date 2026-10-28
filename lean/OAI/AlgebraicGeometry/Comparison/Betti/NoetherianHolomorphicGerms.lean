import OAI.AlgebraicGeometry.Comparison.Betti.GermRegularization
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.GermQuotient
import OAI.AlgebraicGeometry.Comparison.Betti.NoetherianPrincipalQuotients

/-! # Noetherian Holomorphic Germs -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.NoetherianHolomorphicGerms.AnalyticLocal

noncomputable section

/-! Actual holomorphic germ rings in finite-dimensional complex vector
spaces are Noetherian, by preparation and induction on dimension. -/

open Set Filter
open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem holomorphicConstantHom_surjective [Subsingleton E] (x : E) :
    Function.Surjective (Holomorphic.GermMaps.AnalyticLocal.holomorphicConstantHom x) := by
  intro a
  obtain ⟨F, hFa, _⟩ := a.property
  refine ⟨F x, ?_⟩
  apply Subtype.ext
  change ((fun _ : E => F x) : Germ (𝓝 x) ℂ) = a.val
  rw [← hFa]
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall (fun y => congrArg F (Subsingleton.elim x y))

def subsingletonGermEquiv [Subsingleton E] (x : E) : ℂ ≃+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x :=
  RingEquiv.ofBijective (Holomorphic.GermMaps.AnalyticLocal.holomorphicConstantHom x)
    ⟨fun _ _ h => congrArg (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.valueHom x) h, holomorphicConstantHom_surjective x⟩

theorem holomorphic_product_germ_noetherian (n : ℕ)
    [IsNoetherianRing (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (0 : Fin n → ℂ))] (x : Fin n → ℂ) (c : ℂ) :
    IsNoetherianRing (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (x, c)) := by
  apply NoetherianPrincipalQuotients.AnalyticLocal.noetherian_of_nonzero_principal_quotients
  intro a ha
  obtain ⟨e, he⟩ := GermRegularization.AnalyticLocal.exists_regular_germ_coordinate_equiv x c a ha
  let : Module.Finite (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (0 : Fin n → ℂ))
      (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm ((0 : Fin n → ℂ), (0 : ℂ)) ⧸ Ideal.span {e a}) :=
    Betti.Finite.GermQuotient.AnalyticLocal.regular_germ_quotient_finite (0 : Fin n → ℂ) 0 (e a) he
  let : IsNoetherianRing (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm ((0 : Fin n → ℂ), (0 : ℂ)) ⧸ Ideal.span {e a}) :=
    IsNoetherianRing.of_finite (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (0 : Fin n → ℂ)) _
  exact NoetherianPrincipalQuotients.AnalyticLocal.principal_quotient_noetherian_of_equiv e a

theorem holomorphic_fin_germ_noetherian (n : ℕ) (x : Fin n → ℂ) :
    IsNoetherianRing (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x) := by
  induction n with
  | zero => exact isNoetherianRing_of_ringEquiv ℂ (subsingletonGermEquiv x)
  | succ n ih =>
    let L : (Fin (n + 1) → ℂ) ≃L[ℂ] ((Fin n → ℂ) × ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp)
    let e := GermCoordinateEquiv.AnalyticLocal.holomorphicGermEquiv L.toEquiv L.differentiable L.symm.differentiable x
    let : IsNoetherianRing (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (0 : Fin n → ℂ)) := ih 0
    let : IsNoetherianRing (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (L.toEquiv x)) :=
      holomorphic_product_germ_noetherian n (L.toEquiv x).1 (L.toEquiv x).2
    exact isNoetherianRing_of_ringEquiv _ e.symm

theorem holomorphic_germ_noetherian [FiniteDimensional ℂ E] (x : E) :
    IsNoetherianRing (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x) := by
  let L : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let e := GermCoordinateEquiv.AnalyticLocal.holomorphicGermEquiv L.toEquiv L.differentiable L.symm.differentiable x
  let : IsNoetherianRing (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (L.toEquiv x)) := holomorphic_fin_germ_noetherian _ (L.toEquiv x)
  exact isNoetherianRing_of_ringEquiv _ e.symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.NoetherianHolomorphicGerms.AnalyticLocal
