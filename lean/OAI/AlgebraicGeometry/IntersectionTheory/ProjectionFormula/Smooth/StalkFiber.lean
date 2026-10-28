import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.LocalizedBase

/-! # Stalk Fiber -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.StalkFiber

noncomputable section

/-! The closed fiber of each actual stalk map of a smooth morphism
is a domain. The ring map is the native scheme stalk map. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem quotient_domain {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (x : X) :
    IsDomain ((X.presheaf.stalk x) ⧸
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom) := by
  obtain ⟨U, hU, V, hV, hxV, hVU, hsm⟩ := Smooth.exists_isStandardSmooth f x
  let R := Γ(Y, U)
  let A := Γ(X, V)
  let T := Y.presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  let : Algebra R A := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra.Smooth R A := hsm.smooth
  let : Algebra R T := Y.presheaf.algebra_section_stalk ⟨f x, hVU hxV⟩
  let : Algebra A S := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  let : Algebra T S := (f.stalkMap x).hom.toAlgebra
  let : IsLocalHom (algebraMap T S) := f.toLRSHom.prop x
  let : Algebra R S := ((f.stalkMap x).hom.comp (Y.presheaf.germ U (f x) (hVU hxV)).hom).toAlgebra
  let : IsScalarTower R T S := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R A S := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change f.stalkMap x (Y.presheaf.germ U (f x) (hVU hxV) a) =
      X.presheaf.germ V x hxV (f.appLE U V hVU a)
    simp only [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE,
      CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, X.presheaf.germ_res_apply])
  let p := (hU.primeIdealOf ⟨f x, hVU hxV⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let : IsLocalization.AtPrime T p := hU.isLocalization_stalk ⟨f x, hVU hxV⟩
  let : IsLocalization.AtPrime S q := hV.isLocalization_stalk ⟨x, hxV⟩
  have hp : q.comap (algebraMap R A) = p := by
    exact congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV)
  have hNM : Algebra.algebraMapSubmonoid A p.primeCompl ≤ q.primeCompl := by
    rintro _ ⟨a, ha, rfl⟩
    change algebraMap R A a ∉ q
    intro h
    exact ha (show a ∈ p from hp ▸ h)
  exact LocalizedBase.quotient_domain R A T S p.primeCompl q.primeCompl hNM

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.StalkFiber
