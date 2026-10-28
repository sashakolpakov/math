import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.OpenPresentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalAffine
import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Covers
import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Image

/-! # Presentation Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.PresentationCover

noncomputable section

/-!
# IntegralComparison: local small presentations cover the big crystalline site

Every big object has a principal covering whose members admit maps to
small polynomial presentations. This proves cover density of the full
subcategory used in the constant-source descent argument.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
variable (X : Over (Spec (CommRingCat.of k)))

abbrev Big := BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
  (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X)

abbrev inclusion := BigCrystallineSite.fromSmall (p := p) (B := WittVector p k) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (f := Witt.Crystalline.wittStructureMap p k X)

lemma incoming_of_open_range (T : Big p k X) (C : CommRingCat.{u}) (j : Spec C ⟶ X.left)
    [IsOpenImmersion j] (h : Set.range T.mapToX ⊆ Set.range j) :
    Nonempty (StructuredArrow T (inclusion p k X)) := by
  let : Algebra k C := (Spec.preimage (j ≫ X.hom)).hom.toAlgebra
  let j' : (Presentation.affineScheme k C).left ⟶ X.left := j
  have : IsOpenImmersion j' := ‹IsOpenImmersion j›
  have hj : j' ≫ X.hom = (Presentation.affineScheme k C).hom := (Spec.map_preimage _).symm
  let t := IsOpenImmersion.lift j' T.mapToX h
  have ht : t ≫ j' = T.mapToX := IsOpenImmersion.lift_fac j' T.mapToX h
  exact OpenPresentation.incoming_nonempty p k C X j' hj T t ht

lemma principal_incoming (T : Big p k X) (x : Spec (CommRingCat.of T.ring)) :
    ∃ r : T.ring, r ∉ x.asIdeal ∧ Nonempty (StructuredArrow (Localization.object T r) (inclusion p k X)) := by
  obtain ⟨r, C, j, hj, hr, h⟩ := LocalAffine.exists_principal_affine T x
  let : IsOpenImmersion j := hj
  exact ⟨r, hr, incoming_of_open_range p k X (Localization.object T r) C j h⟩

abbrev Functions (T : Big p k X) :=
  {r : T.ring // Nonempty (StructuredArrow (Localization.object T r) (inclusion p k X))}

lemma functions_span_top (T : Big p k X) :
    Ideal.span (Set.range (fun r : Functions p k X T => r.val)) = ⊤ := by
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
  let : M.IsMaximal := hM
  obtain ⟨r, hr, hpres⟩ := principal_incoming p k X T ⟨M, inferInstance⟩
  apply hr
  exact hle (Ideal.subset_span (Set.mem_range.mpr ⟨⟨r, hpres⟩, rfl⟩))

instance incomingImage_coverDense :
    (Incoming.Image.inclusion (inclusion p k X)).IsCoverDense BigCrystallineSite.Object.topology where
  is_cover T := by
    apply BigCrystallineSite.Object.topology.superset_covering _
      (CrystallinePrincipal.Covers.coveringSieve T
        (fun r : Functions p k X T => r.val) (functions_span_top p k X T))
    rw [Sieve.generate_le_iff]
    intro Z α hα
    cases hα with
    | mk r =>
      exact Presieve.in_coverByImage
        (Incoming.Image.inclusion (inclusion p k X))
        (Y := ⟨Localization.object T r.val, r.property⟩) (Localization.hom T r.val)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.PresentationCover
