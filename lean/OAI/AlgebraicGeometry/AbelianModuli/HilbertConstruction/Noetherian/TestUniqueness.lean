import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.FineIsoScheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedPolarizedIsoFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedPolarizedIsoUniversal
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveProducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveParameterCuts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseSquareIsomorphism

/-! # Test Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.TestUniqueness

noncomputable section

/-! The original full-level isomorphism scheme reduces uniqueness of
parameter points on arbitrary test schemes to uniqueness on Noetherian
tests. The universal isomorphism is tested on its actual finite-type
parameter scheme, so nilpotents in the test scheme are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u

theorem noetherian_polarizedIso_noetherian_representation
    {S : Scheme.{u}} [IsNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) :
    ∃ M : Over S, IsNoetherian M.left ∧
      Nonempty (Family.LevelIsoFunctor.familyLevelIsoFunctor A B ≅ yoneda.obj M) := by
  obtain ⟨M, ⟨e⟩, _⟩ := LocallyNoetherian.FineIsoScheme.locallyNoetherian_polarizedIso_scheme_representation A B hδ hN
  obtain ⟨ht, hq⟩ := RepresentedPolarizedIsoFiniteness.representedPolarizedIsoParameter_finiteType A B hδ hN M e
  let : LocallyOfFiniteType M.hom := ht
  let : QuasiCompact M.hom := hq
  let : IsLocallyNoetherian M.left := LocallyOfFiniteType.isLocallyNoetherian M.hom
  let : CompactSpace M.left := QuasiCompact.compactSpace_of_compactSpace M.hom
  exact ⟨M, ⟨⟩, ⟨e⟩⟩

private theorem factor_equal_composites
    {C : Type*} [Category* C] {I Y Z T : C}
    (q : I ⟶ Y) (a b : Y ⟶ Z) (h : q ≫ a = q ≫ b)
    (k : T ⟶ I) (c : T ⟶ Y) (hc : k ≫ q = c) : c ≫ a = c ≫ b := by
  rw [← hc, Category.assoc, Category.assoc, h]

/-- For a fixed quasi-projective parameter with its original universal
family, uniqueness on Noetherian tests implies uniqueness on every
test scheme. No representability of the moduli problem is assumed. -/
theorem polarizedParameterPoints_eq_of_noetherianTests
    {S : Scheme.{u}} [IsNoetherian S] {X : Over S}
    (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation X) {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N X.left)
    (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
    (huniq : ∀ (V : Over S), IsNoetherian V.left → ∀ (a b : V ⟶ X),
      Nonempty (Moduli.Isomorphisms.LevelPreservingIso (A.pullback a.left) (A.pullback b.left)) → a = b)
    {T : Over S} (a b : T ⟶ X)
    (hab : Nonempty (Moduli.Isomorphisms.LevelPreservingIso (A.pullback a.left) (A.pullback b.left))) :
    a = b := by
  let Y := X ⊗ X
  let p : Y ⟶ X := fst X X
  let q : Y ⟶ X := snd X X
  let : IsNoetherian Y.left := (Q.product Q).noetherian
  let A₁ := A.pullback p.left
  let A₂ := A.pullback q.left
  obtain ⟨I, hI, ⟨e⟩⟩ := noetherian_polarizedIso_noetherian_representation A₁ A₂ hδ hN
  let V : Over S := Over.mk (I.hom ≫ Y.hom)
  let v : V ⟶ Y := Over.homMk I.hom rfl
  let r := RepresentedPolarizedIsoUniversal.representedUniversalLevelIso A₁ A₂ I e
  have hv : v ≫ p = v ≫ q := huniq V hI (v ≫ p) (v ≫ q)
    ⟨((Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A p.left I.hom).symm.trans r).trans
      (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A q.left I.hom)⟩
  let c : T ⟶ Y := lift a b
  have hca : c ≫ p = a := lift_fst a b
  have hcb : c ≫ q = b := lift_snd a b
  let ca : Moduli.Isomorphisms.LevelPreservingIso (A₁.pullback c.left) (A.pullback a.left) :=
    (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A p.left c.left).trans
      (Moduli.Isomorphisms.LevelPreservingIso.ofEqualBaseMaps A (c.left ≫ p.left) a.left
        (congrArg Over.Hom.left hca))
  let cb : Moduli.Isomorphisms.LevelPreservingIso (A₂.pullback c.left) (A.pullback b.left) :=
    (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A q.left c.left).trans
      (Moduli.Isomorphisms.LevelPreservingIso.ofEqualBaseMaps A (c.left ≫ q.left) b.left
        (congrArg Over.Hom.left hcb))
  obtain ⟨r₀⟩ := hab
  let k : Over.mk c.left ⟶ I := e.hom.app (.op (Over.mk c.left)) ((ca.trans r₀).trans cb.symm)
  have hfactor : c.left ≫ p.left = c.left ≫ q.left :=
    factor_equal_composites I.hom p.left q.left (congrArg Over.Hom.left hv)
      k.left c.left k.w
  apply Over.OverMorphism.ext
  exact (congrArg Over.Hom.left hca).symm.trans (hfactor.trans (congrArg Over.Hom.left hcb))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.TestUniqueness
