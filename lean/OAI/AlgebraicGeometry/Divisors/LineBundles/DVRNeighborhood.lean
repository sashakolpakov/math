import OAI.AlgebraicGeometry.Divisors.LineBundles.DVRMultiplicity

/-! # DVR Neighborhood -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.DVRNeighborhood.BundleCycles

noncomputable section

/-!
# LineBundleCycles: regular neighborhood equations for DVR factorizations

A unit in a local ring has an actual unit representative on an affine
neighborhood. Combining this with a regular representative of a uniformizer
lifts the DVR factorization of a rational function to regular functions on
one affine open, with exponent equal to its actual algebraic divisor order.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

universe u

/-- A local unit is represented by a genuine regular unit on an affine neighborhood. -/
theorem stalkUnit_affine_representative (X : Scheme.{u}) (x : X) (u : (X.presheaf.stalk x)ˣ) :
    ∃ (U : X.Opens) (_ : U ∈ X.affineOpens) (hxU : x ∈ U) (v : Γ(X, U)ˣ),
      X.presheaf.germ U x hxU v = u := by
  obtain ⟨W, hxW, a, ha⟩ := X.presheaf.exists_germ_eq (u : X.presheaf.stalk x)
  obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
  let aA : Γ(X, A) := X.presheaf.map (homOfLE hAW).op a
  have haA : X.presheaf.germ A x hxA aA = u :=
    (X.presheaf.germ_res_apply (homOfLE hAW) x hxA a).trans ha
  have hxU : x ∈ X.basicOpen aA := by
    apply (Scheme.mem_basicOpen X aA x hxA).mpr
    exact haA.symm ▸ u.isUnit
  obtain ⟨v, hv⟩ := X.toRingedSpace.isUnit_res_basicOpen aA
  refine ⟨X.basicOpen aA, hA.basicOpen aA, hxU, v, ?_⟩
  rw [hv]
  exact (X.presheaf.germ_res_apply (homOfLE (X.basicOpen_le aA)) x hxU aA).trans haA

/-- A local element and a local unit admit simultaneous regular representatives
on one actual affine neighborhood. -/
theorem stalkElement_unit_affine_representatives (X : Scheme.{u}) (x : X)
    (π : X.presheaf.stalk x) (u : (X.presheaf.stalk x)ˣ) :
    ∃ (U : X.Opens) (_ : U ∈ X.affineOpens) (hxU : x ∈ U)
      (p : Γ(X, U)) (v : Γ(X, U)ˣ),
      X.presheaf.germ U x hxU p = π ∧ X.presheaf.germ U x hxU v = u := by
  obtain ⟨P, hxP, p, hp⟩ := X.presheaf.exists_germ_eq π
  obtain ⟨V, _, hxV, v, hv⟩ := stalkUnit_affine_representative X x u
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUPV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ P ⊓ V from ⟨hxP, hxV⟩) (P ⊓ V).isOpen
  let hUP : U ≤ P := hUPV.trans inf_le_left
  let hUV : U ≤ V := hUPV.trans inf_le_right
  refine ⟨U, hU, hxU, X.presheaf.map (homOfLE hUP).op p,
    Units.map (X.presheaf.map (homOfLE hUV).op).hom.toMonoidHom v, ?_, ?_⟩
  · exact (X.presheaf.germ_res_apply (homOfLE hUP) x hxU p).trans hp
  · exact (X.presheaf.germ_res_apply (homOfLE hUV) x hxU (v : Γ(X, V))).trans hv

/-- The actual divisor coefficient is the exponent in an equality of rational
functions represented by a regular equation and a unit on an affine neighborhood. -/
theorem rationalFunction_DVR_neighborhood (X : Scheme.{u}) [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (x : X) (hx : coheight x = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (π : X.presheaf.stalk x) (hπ : Irreducible π) (f : X.functionField) (hf : f ≠ 0) :
    ∃ (U : X.Opens) (_ : U ∈ X.affineOpens) (hxU : x ∈ U)
      (p : Γ(X, U)) (v : Γ(X, U)ˣ),
      X.presheaf.germ U x hxU p = π ∧
      letI : Nonempty U := ⟨⟨x, hxU⟩⟩
      f = X.germToFunctionField U v * (X.germToFunctionField U p) ^ (X.ord f x) := by
  obtain ⟨u, hu⟩ := DVRMultiplicity.BundleCycles.rationalFunction_DVR_factorization X x hx π hπ f hf
  obtain ⟨U, hU, hxU, p, v, hp, hv⟩ := stalkElement_unit_affine_representatives X x π u
  refine ⟨U, hU, hxU, p, v, hp, ?_⟩
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hpF : X.germToFunctionField U p = algebraMap (X.presheaf.stalk x) X.functionField π :=
    (Scheme.algebraMap_germ_eq_germToFunctionField X hxU p).symm.trans
      (congrArg (algebraMap (X.presheaf.stalk x) X.functionField) hp)
  have hvF : X.germToFunctionField U v = algebraMap (X.presheaf.stalk x) X.functionField u :=
    (Scheme.algebraMap_germ_eq_germToFunctionField X hxU (v : Γ(X, U))).symm.trans
      (congrArg (algebraMap (X.presheaf.stalk x) X.functionField) hv)
  rw [hpF, hvF]
  exact hu

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.DVRNeighborhood.BundleCycles
