import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothDVR
import OAI.AlgebraicGeometry.Divisors.LineBundles.DVRNeighborhood
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.Coordinates

/-! # Divisor Equations -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorEquations.Constructions

noncomputable section

/-!
# DegreeTwo: actual local equations with the algebraic divisor multiplicity

Smoothness supplies the DVR at a codimension-one point. Its uniformizer and
unit lift to an affine neighborhood inside any specified open. The exponent
is the existing algebraic order, and for a bundle section it is exactly the
coefficient of its already constructed rational-section divisor.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

universe u

/-- A nonzero rational function on a smooth integral scheme is, near a
codimension-one point, a regular unit times a uniformizer to its actual order. -/
theorem smooth_rationalFunction_local_equation {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [Smooth f] (x : X) (hx : coheight x = 1)
    (V : X.Opens) (hxV : x ∈ V) (g : X.functionField) (hg : g ≠ 0) :
    ∃ (U : X.Opens) (_ : U ∈ X.affineOpens) (hxU : x ∈ U) (_ : U ≤ V)
      (p : Γ(X, U)) (v : Γ(X, U)ˣ),
      Irreducible (X.presheaf.germ U x hxU p) ∧
      letI : Nonempty U := ⟨⟨x, hxU⟩⟩
      g = X.germToFunctionField U v * (X.germToFunctionField U p) ^ (X.ord g x) := by
  let : IsDiscreteValuationRing (X.presheaf.stalk x) := SmoothDVR.Constructions.smoothScheme_stalk_isDiscreteValuationRing f x hx
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x)
  obtain ⟨W, _, hxW, p, v, hp, he⟩ :=
    Divisors.LineBundles.DVRNeighborhood.BundleCycles.rationalFunction_DVR_neighborhood X x hx π hπ g hg
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUWV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ W ⊓ V from ⟨hxW, hxV⟩) (W ⊓ V).isOpen
  let hUW : U ≤ W := hUWV.trans inf_le_left
  let q : Γ(X, U) := X.presheaf.map (homOfLE hUW).op p
  let w : Γ(X, U)ˣ := Units.map (X.presheaf.map (homOfLE hUW).op).hom.toMonoidHom v
  refine ⟨U, hU, hxU, hUWV.trans inf_le_right, q, w, ?_, ?_⟩
  · have hq : X.presheaf.germ U x hxU q = π :=
      (X.presheaf.germ_res_apply (homOfLE hUW) x hxU p).trans hp
    rw [hq]
    exact hπ
  · let : Nonempty U := ⟨⟨x, hxU⟩⟩
    let : Nonempty W := ⟨⟨x, hxW⟩⟩
    change g = X.germToFunctionField U
        (X.presheaf.map (homOfLE hUW).op (v : Γ(X, W))) *
      (X.germToFunctionField U (X.presheaf.map (homOfLE hUW).op p)) ^ (X.ord g x)
    rw [DivisorClass.Chern.Rational.Coordinates.Construction.germToFunctionField_restrict,
      DivisorClass.Chern.Rational.Coordinates.Construction.germToFunctionField_restrict]
    exact he

/-- For the actual rational section, this exponent is precisely the
already-defined divisor coefficient, in any algebraic frame through the point. -/
theorem rationalSection_local_equation {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (L : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle X) [IsIntegral X.carrier]
    (x : X.carrier) (hx : coheight x = 1) (i : X.carrier) (hxi : x ∈ L.trivializingOpen i) :
    ∃ (U : X.carrier.Opens) (_ : U ∈ X.carrier.affineOpens) (hxU : x ∈ U)
      (_ : U ≤ L.trivializingOpen i) (p : Γ(X.carrier, U)) (v : Γ(X.carrier, U)ˣ),
      Irreducible (X.carrier.presheaf.germ U x hxU p) ∧
      letI : Nonempty U := ⟨⟨x, hxU⟩⟩
      (L.rationalSectionCoordinate i : X.carrier.functionField) =
        X.carrier.germToFunctionField U v *
          (X.carrier.germToFunctionField U p) ^ (L.rationalSectionOrder x) := by
  let : Smooth X.structureMap := X.smooth
  obtain ⟨U, hU, hxU, hUi, p, v, hp, he⟩ := smooth_rationalFunction_local_equation
    X.structureMap x hx (L.trivializingOpen i) hxi (L.rationalSectionCoordinate i)
      (L.rationalSectionCoordinate_ne_zero i)
  refine ⟨U, hU, hxU, hUi, p, v, hp, ?_⟩
  rw [L.rationalSectionOrder_in_chart x i hxi]
  exact he

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorEquations.Constructions
