import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Affine Rational Of -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineRationalOf.Construction.AffineRationalDomain

noncomputable section

/-! An affine open in an integral separated scheme is the domain of its rational coordinate ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem lift_ringHom {R S F : Type*} [CommRing R] [CommRing S] [CommRing F]
    (α : S →+* F) (hα : Function.Injective α) (γ : R →+* F)
    (h : ∀ a : R, ∃ b : S, α b = γ a) :
    ∃ ρ : R →+* S, α.comp ρ = γ := by
  choose ρ hρ using h
  refine ⟨{ toFun := ρ
            map_one' := hα (by rw [hρ, map_one, map_one])
            map_mul' := fun a b => hα (by rw [hρ, map_mul, map_mul, hρ, hρ])
            map_zero' := hα (by rw [hρ, map_zero, map_zero])
            map_add' := fun a b => hα (by rw [hρ, map_add, map_add, hρ, hρ]) }, ?_⟩
  ext a
  exact hρ a

theorem mem_of_regular_coordinates {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    (U : X.affineOpens) [Nonempty U.1] (x : X)
    (h : ∀ a : Γ(X, U), ∃ b : X.presheaf.stalk x,
      algebraMap _ X.functionField b = X.germToFunctionField U.1 a) : x ∈ U.1 := by
  let α : (X.presheaf.stalk x) →+* X.functionField := algebraMap _ _
  have hα : Function.Injective α := IsFractionRing.injective _ _
  obtain ⟨ρ, hρ⟩ := lift_ringHom α hα (X.germToFunctionField U.1).hom h
  let j : Spec X.functionField ⟶ Spec (X.presheaf.stalk x) := Spec.map (CommRingCat.ofHom α)
  have : IsDominant j := by
    refine ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical α).mpr ?_⟩
    rw [(RingHom.injective_iff_ker_eq_bot α).mp hα]
    exact bot_le
  let k : Spec (X.presheaf.stalk x) ⟶ X := Spec.map (CommRingCat.ofHom ρ) ≫ U.2.fromSpec
  have he : j ≫ k = j ≫ X.fromSpecStalk x := by
    have hg : j ≫ X.fromSpecStalk x = X.fromSpecStalk (genericPoint X) :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec X).specializes (Set.mem_univ x))
    rw [hg]
    change Spec.map (CommRingCat.ofHom α) ≫ Spec.map (CommRingCat.ofHom ρ) ≫ U.2.fromSpec = _
    rw [← Spec.map_comp_assoc]
    have heq : CommRingCat.ofHom ρ ≫ CommRingCat.ofHom α = X.germToFunctionField U.1 := by
      apply CommRingCat.hom_ext
      exact hρ
    rw [heq]
    exact U.2.fromSpecStalk_eq_fromSpecStalk
      (((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr
        ⟨(inferInstance : Nonempty U.1).some.1, Set.mem_univ _,
          (inferInstance : Nonempty U.1).some.2⟩)
  have hk : k = X.fromSpecStalk x := ext_of_isDominant j he
  have hx : k (IsLocalRing.closedPoint (X.presheaf.stalk x)) = x := by
    rw [hk, Scheme.fromSpecStalk_closedPoint]
  rw [← hx]
  change U.2.fromSpec ((Spec.map (CommRingCat.ofHom ρ))
    (IsLocalRing.closedPoint (X.presheaf.stalk x))) ∈ U.1
  exact (Set.ext_iff.mp U.2.range_fromSpec _).mp (Set.mem_range_self _)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineRationalOf.Construction.AffineRationalDomain
