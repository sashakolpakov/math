import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BaseCoverVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.CartesianCohomology

/-! # Open Base Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual Poincare family has zero cohomology over every separated locally Noetherian parameter scheme disjoint from the zero section. Affine opens supply the local calculation and an actual Cech cover supplies its globalization. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem Dual.Data.DualAbelianData.poincare_cartesian_cohomology_vanish_off_zero
    {S T : Scheme.{u}} [T.IsSeparated] [IsLocallyNoetherian T]
    {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S} (D : Dual.Data.DualAbelianData A)
    (t : T ⟶ D.abelian.scheme.left)
    (hoff : t ⁻¹' Set.range η[D.abelian.scheme].left = ∅)
    {P : Scheme.{u}} {a : P ⟶ (D.abelian.scheme ⊗ A.scheme).left} {b : P ⟶ T}
    (H : IsPullback a b (pullback.fst D.abelian.scheme.hom A.scheme.hom) t) (q : ℕ) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (D.poincare.pullback a).sheaf q) := by
  let M := (D.poincare.pullback a).sheaf
  apply Affine.BaseCoverVanishing.cohomology_vanish_of_affine_base_opens b M
  intro V hV n
  have : IsAffine V.toScheme := hV
  have : IsNoetherianRing Γ(V.toScheme, ⊤) :=
    isLocallyNoetherian_Spec.mp (isLocallyNoetherian_of_isOpenImmersion V.toScheme.isoSpec.inv)
  let W := b ⁻¹ᵁ V
  let a' := W.ι ≫ a
  let b' := b ∣_ V
  let t' := V.ι ≫ t
  have H' : IsPullback a' b' (pullback.fst D.abelian.scheme.hom A.scheme.hom) t' :=
    ((isPullback_morphismRestrict b V).paste_vert H.flip).flip
  have hoff' : t' ⁻¹' Set.range η[D.abelian.scheme].left = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h : V.ι x ∈ t ⁻¹' Set.range η[D.abelian.scheme].left := hx
    rw [hoff] at h
    exact h
  have hzero := D.poincareAffine_cartesian_cohomology_vanish_off_zero t' hoff' H' n
  have : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (D.poincare.pullback a').sheaf n) :=
    ModuleCat.subsingleton_of_isZero hzero
  let e : M.restrict W.ι ≅ (D.poincare.pullback a').sheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback W.ι).app M ≪≫
      (Scheme.Modules.pullbackComp W.ι a).app D.poincare.sheaf
  exact ((Zariski.Cohomology.ZariskiCohomology.zariskiFunctor W.toScheme n).mapIso e).addCommGroupIsoToAddEquiv.injective.subsingleton

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
