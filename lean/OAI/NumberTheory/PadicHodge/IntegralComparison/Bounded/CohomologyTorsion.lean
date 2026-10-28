import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.StructureDescent

/-! # Cohomology Torsion -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CohomologyTorsion

noncomputable section

/-!
# IntegralComparison: the level bound annihilates actual bounded crystalline cohomology

The original structure sheaf restricted to level n is killed by p^(n+1).
The same bound therefore annihilates its actual Ext cohomology in every
degree, using the original coefficient action.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ)

def structurePresheafIso :
    (BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n).op ⋙
      BigCrystallineCohomology.largePresheaf f ≅ (BoundedCrystalline.CrystallineCohomology.structureSheaf f n).obj :=
  Functor.isoWhiskerLeft (BoundedCrystalline.Site.inclusion f n).op
    (Crystalline.StructureDescent.structurePresheafIso f)

theorem presheaf_smul_zero (U : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
    (a : (BigCrystallineCohomology.largePresheaf f).obj (op U.obj)) :
    ((p : Crystalline.ExactRestriction.Coeff (B := B)) ^ (n + 1)) • a = 0 := by
  apply ULift.ext
  change @Mul.mul U.obj.ring _ (U.obj.base ((p : B) ^ (n + 1))) a.down = 0
  rw [map_pow, map_natCast, U.property]
  exact @zero_mul U.obj.ring inferInstance a.down

theorem structureSheaf_smul_zero : ((p : Crystalline.ExactRestriction.Coeff (B := B)) ^ (n + 1)) •
    𝟙 (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f n) = 0 := by
  apply (sheafToPresheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).map_injective
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let e := (structurePresheafIso (p := p) (J := J) (δ := δ) f n).app U
  obtain ⟨a, rfl⟩ := e.toLinearEquiv.surjective x
  change ((p : Crystalline.ExactRestriction.Coeff (B := B)) ^ (n + 1)) • e.hom a = 0
  rw [← map_smul, presheaf_smul_zero f n U.unop a, map_zero]

theorem cohomology_smul_zero (i : ℕ) (x : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i) :
    ((p : Crystalline.ExactRestriction.Coeff (B := B)) ^ (n + 1)) • x = 0 := by
  rw [Abelian.Ext.smul_eq_comp_mk₀, structureSheaf_smul_zero]
  simp

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CohomologyTorsion
