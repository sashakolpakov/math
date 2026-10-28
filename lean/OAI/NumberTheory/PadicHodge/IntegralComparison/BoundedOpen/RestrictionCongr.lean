import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Subsite

/-! # Restriction Congr -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.RestrictionCongr

noncomputable section

/-! Equality of geometric opens transports the original incoming
restriction properties without changing its coefficient categories. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  {K L : CochainComplex
    (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n) ℕ}
  (a : K ⟶ L) (V V' : Y.Opens) (h : V = V')

include h in
theorem isIso
    (hV : IsIso (((Subsite.restriction fY V.ι n).mapHomologicalComplex (.up ℕ)).map a)) :
    IsIso (((Subsite.restriction fY V'.ι n).mapHomologicalComplex (.up ℕ)).map a) := by
  subst V'
  exact hV

include h in
theorem quasiIso
    (hV : QuasiIso (((Subsite.restriction fY V.ι n).mapHomologicalComplex (.up ℕ)).map a)) :
    QuasiIso (((Subsite.restriction fY V'.ι n).mapHomologicalComplex (.up ℕ)).map a) := by
  subst V'
  exact hV

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.RestrictionCongr
