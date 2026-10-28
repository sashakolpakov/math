import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SheafInjectives

/-! # Open Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.OpenCohomology

noncomputable section

/-!
# IntegralComparison: cohomology of the geometric subsite is the original bounded chart cohomology
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (g : X ⟶ Y) (n : ℕ)

instance hasExt : HasExt.{u + 2} (Subsite.ModuleSheaf (p := p) (J := J) (δ := δ) fY g n) :=
  HasExt.standard _

abbrev Cohomology (i : ℕ) := Abelian.Ext.{u + 2}
  (Sheaves.constantUnit (p := p) (J := J) (δ := δ) fY g n)
  (Sheaves.structureSheaf fY g n) i

variable {fY} {f : X ⟶ Spec (CommRingCat.of B)} [Mono g] (hg : g ≫ fY = f)

def cohomologyEquiv (i : ℕ) : Cohomology (p := p) (J := J) (δ := δ) fY g n i ≃ₗ[Crystalline.ExactRestriction.Coeff (B := B)]
    BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i :=
  (LinearEquiv.ofBijective
    ((Sheaves.equivalence g hg n).functor.mapExtLinearMap (Crystalline.ExactRestriction.Coeff (B := B))
      (Sheaves.constantUnit fY g n) (Sheaves.structureSheaf fY g n) i)
    ((Sheaves.equivalence g hg n).functor.mapExt_bijective_of_preservesInjectiveObjects
      (Sheaves.constantUnit fY g n) (Sheaves.structureSheaf fY g n) i)).trans
    (Etale.Frobenius.extIsoCongr (Crystalline.ExactRestriction.Coeff (B := B))
      (Sheaves.constantUnitIso g hg n) (Sheaves.structureSheafIso g hg n) i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.OpenCohomology
