import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Covers

/-! # Principal Covers -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PrincipalCovers

noncomputable section

/-!
# IntegralComparison: principal coverings in the actual bounded crystalline site
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u v

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {n : ℕ}
  (U : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

def object (r : U.obj.ring) : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n :=
  ⟨Crystalline.Localization.object U.obj r,
    BoundedCrystalline.Site.property_of_hom f n (Crystalline.Localization.hom U.obj r) U.property⟩

def hom (r : U.obj.ring) : object U r ⟶ U :=
  ObjectProperty.homMk (Crystalline.Localization.hom U.obj r)

variable {ι : Type v} (r : ι → U.obj.ring)

def presieve : Presieve U := Presieve.ofArrows (fun i => object U (r i)) (fun i => hom U (r i))

theorem map_presieve : (presieve U r).map (BoundedCrystalline.Site.inclusion f n) =
    CrystallinePrincipal.Covers.presieve U.obj r := by
  rw [presieve, Presieve.map_ofArrows]
  rfl

theorem coveringSieve (hr : Ideal.span (Set.range r) = ⊤) :
    Sieve.generate (presieve U r) ∈ BoundedCrystalline.Site.topology f n U := by
  apply Functor.mem_restrictedTopology_of_functorPushforward_mem
  rw [← Sieve.generate_map_eq_functorPushforward, map_presieve]
  exact CrystallinePrincipal.Covers.coveringSieve U.obj r hr

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PrincipalCovers
