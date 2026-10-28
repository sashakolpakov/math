import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Covering
import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.CoverDescent
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Section Sheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSheaf

noncomputable section

/-!
# IntegralComparison: geometric open sections form a sheaf for the original bounded crystalline coefficients
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Support
open OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (F : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n)

theorem isSheaf : Presheaf.IsSheaf (Opens.grothendieckTopology Y)
    ((SectionPresheaf.functor fY n).obj F) := by
  let : Limits.HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) :=
    ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing
    (C := ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) (X := Y.carrier)
      ((SectionPresheaf.functor fY n).obj F)).mpr
  intro ι V a ha
  let P := fun i => SectionPresheaf.property (p := p) (J := J) (δ := δ) fY n (V i)
  let Q := SectionPresheaf.property (p := p) (J := J) (δ := δ) fY n (iSup V)
  have hP : ∀ i {U T : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n},
      (U ⟶ T) → P i T → P i U := fun i {_ _} α => SectionPresheaf.incoming fY n (V i) α
  have hPQ : ∀ i, P i ≤ Q := fun i => SectionPresheaf.monotone fY n (le_iSup V i)
  have hcover : ∀ T, Q T → Incoming.CoverFamily.Family.sieve P hP T ∈
      BoundedCrystalline.Site.topology fY n T := by
    intro T hT
    change Covering.sieve V T ∈ BoundedCrystalline.Site.topology fY n T
    apply Covering.covering V T
    intro z
    have hz : T.obj.mapToX z ∈ iSup V :=
      (Support.property_iff_range_subset fY n T (iSup V)).mp hT ⟨z, rfl⟩
    exact TopologicalSpace.Opens.mem_iSup.mp hz
  have hac : Incoming.CoverFamily.Family.Compatible (Crystalline.ExactRestriction.Coeff (B := B))
      (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B)) (Crystalline.ExactRestriction.Coeff (B := B))) P F.obj a := by
    intro i j T hi hj
    have hT : SectionPresheaf.property fY n (V i ⊓ V j) T := (Support.property_inf fY n T (V i) (V j)).mpr ⟨hi, hj⟩
    exact congrArg (fun t : Incoming.SectionRestriction.Sections (Crystalline.ExactRestriction.Coeff (B := B))
      (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B)) (Crystalline.ExactRestriction.Coeff (B := B))) (SectionPresheaf.property fY n (V i ⊓ V j)) F.obj =>
        t.app (op ⟨T, hT⟩)) (ha i j)
  exact Incoming.CoverDescent.existsUnique (Crystalline.ExactRestriction.Coeff (B := B))
    (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B)) (Crystalline.ExactRestriction.Coeff (B := B))) P hP Q hPQ
      (BoundedCrystalline.Site.topology fY n) hcover F a hac

def sheaf : Sheaf (Opens.grothendieckTopology Y) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) :=
  ⟨(SectionPresheaf.functor fY n).obj F, isSheaf fY n F⟩

omit F in
def functor : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n ⥤
    Sheaf (Opens.grothendieckTopology Y) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) :=
  ObjectProperty.lift _ (SectionPresheaf.functor fY n) (isSheaf fY n)

omit F in
instance functor_additive : (functor (p := p) (J := J) (δ := δ) fY n).Additive where
  map_add := by intros; rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSheaf
