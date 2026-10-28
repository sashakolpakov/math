import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.OpenBaseVanishing

/-! # Cartesian Restriction Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Restricting an actual Cartesian Poincare family to a parameter open
disjoint from the inverse image of zero kills all its cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem Dual.Data.DualAbelianData.poincare_cartesian_openRestriction_vanish
    {S T : Scheme.{u}} [T.IsSeparated] [IsLocallyNoetherian T]
    {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S} (D : Dual.Data.DualAbelianData A)
    {t : T ⟶ D.abelian.scheme.left}
    {P : Scheme.{u}} {a : P ⟶ (D.abelian.scheme ⊗ A.scheme).left} {b : P ⟶ T}
    (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.scheme.hom) t)
    (V : T.Opens) (hoff : (V.ι ≫ t) ⁻¹' Set.range η[D.abelian.scheme].left = ∅) (q : ℕ) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H ((D.poincare.pullback a).sheaf.restrict (b ⁻¹ᵁ V).ι) q) := by
  let W := b ⁻¹ᵁ V
  have : V.toScheme.IsSeparated := ⟨by rw [← terminal.comp_from V.ι]; infer_instance⟩
  have : IsLocallyNoetherian V.toScheme := LocallyOfFiniteType.isLocallyNoetherian V.ι
  have H' : IsPullback (W.ι ≫ a) (b ∣_ V)
      (pullback.fst D.abelian.scheme.hom A.scheme.hom) (V.ι ≫ t) :=
    ((isPullback_morphismRestrict b V).paste_vert H.flip).flip
  have : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (D.poincare.pullback (W.ι ≫ a)).sheaf q) :=
    D.poincare_cartesian_cohomology_vanish_off_zero (V.ι ≫ t) hoff H' q
  let e : ((D.poincare.pullback a).sheaf.restrict W.ι) ≅ (D.poincare.pullback (W.ι ≫ a)).sheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback W.ι).app (D.poincare.pullback a).sheaf ≪≫
      (Scheme.Modules.pullbackComp W.ι a).app D.poincare.sheaf
  exact ((Zariski.Cohomology.ZariskiCohomology.zariskiFunctor W.toScheme q).mapIso e).addCommGroupIsoToAddEquiv.injective.subsingleton

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
