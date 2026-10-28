import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelationLift

/-! # Equalizer -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Equalizer

noncomputable section

/-!
# IntegralComparison: crystalline equalizers for maps agreeing on the closed subscheme

The equalizer is the quotient by the divided-power closure of the
differences of the two ring maps. It has the original closed subscheme,
and its universal property holds in the actual crystalline category.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
variable {U V : BigCrystallineSite.Object p B J δ f} (α β : U ⟶ V)

def relations : Set U.ring := Set.range (fun x : V.ring => α.ringMap x - β.ringMap x)

variable (hq : BigCrystallineSite.Object.quotientMap U V α.ringMap = BigCrystallineSite.Object.quotientMap U V β.ringMap)

include hq in
lemma relations_subset : relations α β ⊆ U.ideal := by
  rintro _ ⟨x, rfl⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub]
  exact sub_eq_zero.mpr (DFunLike.congr_fun hq (Ideal.Quotient.mk V.ideal x))

abbrev object := RelationQuotient.object U (relations α β) (relations_subset α β hq)

def hom : object α β hq ⟶ U :=
  RelationQuotient.hom U (relations α β) (relations_subset α β hq)

lemma condition : hom α β hq ≫ α = hom α β hq ≫ β := by
  apply BigCrystallineSite.Object.Hom.ext
  apply DFunLike.ext
  intro x
  change (RelationQuotient.quotientRingMap U (relations α β)) (α.ringMap x) =
    (RelationQuotient.quotientRingMap U (relations α β)) (β.ringMap x)
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (DividedPower.Relations.relation_mem U.dividedPowers (relations α β)
      (relations_subset α β hq) ⟨x, rfl⟩)

variable {W : BigCrystallineSite.Object p B J δ f} (γ : W ⟶ U) (hγ : γ ≫ α = γ ≫ β)

include hγ in
lemma kills_relations : ∀ x ∈ relations α β, γ.ringMap x = 0 := by
  rintro _ ⟨x, rfl⟩
  change γ.ringMap.toRingHom (α.ringMap x - β.ringMap x) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg (fun t : W ⟶ V => t.ringMap x) hγ)

def lift : W ⟶ object α β hq :=
  RelationLift.liftHom (relations α β) (relations_subset α β hq)
    γ (kills_relations α β γ hγ)

lemma lift_comp : lift α β hq γ hγ ≫ hom α β hq = γ :=
  RelationLift.liftHom_comp (relations α β) (relations_subset α β hq)
    γ (kills_relations α β γ hγ)

lemma lift_unique (l : W ⟶ object α β hq) (hl : l ≫ hom α β hq = γ) : l = lift α β hq γ hγ :=
  RelationLift.liftHom_unique (relations α β) (relations_subset α β hq)
    γ (kills_relations α β γ hγ) l hl

def fork : Fork α β := Fork.ofι (hom α β hq) (Equalizer.condition α β hq)

def isEqualizer : IsLimit (fork α β hq) :=
  Fork.IsLimit.mk _ (fun s => lift α β hq s.ι s.condition)
    (fun s => lift_comp α β hq s.ι s.condition)
    (fun s l hl => lift_unique α β hq s.ι s.condition l hl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Equalizer
