import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.ChartSectionFunctorIso

/-! # Image Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.ImageRestriction

noncomputable section

/-! Geometric restriction to an open chart and restriction to the
incoming subsite on its image detect the same isomorphisms and
quasi-isomorphisms of the original sheaf complexes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)}
  {fY : Y ⟶ Spec (CommRingCat.of B)} (g : X ⟶ Y) [IsOpenImmersion g]
  (hg : g ≫ fY = fX) (n : ℕ)

theorem property_eq : Subsite.property (p := p) (J := J) (δ := δ) fY g n =
    Subsite.property (p := p) (J := J) (δ := δ) fY g.opensRange.ι n := by
  funext T
  exact propext (Bounded.ChartOpenImage.property_iff fY g n T)

variable {K L : CochainComplex
  (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n) ℕ}
  (a : K ⟶ L)

private theorem isIso_congr
    (P Q : ObjectProperty (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n))
    [P.ι.IsContinuous (P.ι.restrictedTopology (BoundedCrystalline.Site.topology fY n))
      (BoundedCrystalline.Site.topology fY n)]
    [Q.ι.IsContinuous (Q.ι.restrictedTopology (BoundedCrystalline.Site.topology fY n))
      (BoundedCrystalline.Site.topology fY n)]
    (h : P = Q)
    (hP : IsIso (((P.ι.sheafPushforwardContinuous
      (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
      (P.ι.restrictedTopology (BoundedCrystalline.Site.topology fY n))
      (BoundedCrystalline.Site.topology fY n)).mapHomologicalComplex (.up ℕ)).map a)) :
    IsIso (((Q.ι.sheafPushforwardContinuous
      (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
      (Q.ι.restrictedTopology (BoundedCrystalline.Site.topology fY n))
      (BoundedCrystalline.Site.topology fY n)).mapHomologicalComplex (.up ℕ)).map a) := by
  subst Q
  exact hP

private theorem quasiIso_congr
    (P Q : ObjectProperty (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n))
    [P.ι.IsContinuous (P.ι.restrictedTopology (BoundedCrystalline.Site.topology fY n))
      (BoundedCrystalline.Site.topology fY n)]
    [Q.ι.IsContinuous (Q.ι.restrictedTopology (BoundedCrystalline.Site.topology fY n))
      (BoundedCrystalline.Site.topology fY n)]
    (h : P = Q)
    (hP : QuasiIso (((P.ι.sheafPushforwardContinuous
      (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
      (P.ι.restrictedTopology (BoundedCrystalline.Site.topology fY n))
      (BoundedCrystalline.Site.topology fY n)).mapHomologicalComplex (.up ℕ)).map a)) :
    QuasiIso (((Q.ι.sheafPushforwardContinuous
      (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
      (Q.ι.restrictedTopology (BoundedCrystalline.Site.topology fY n))
      (BoundedCrystalline.Site.topology fY n)).mapHomologicalComplex (.up ℕ)).map a) := by
  subst Q
  exact hP

theorem isIso
    (h : IsIso (((Bounded.PostcomposeTopology.restriction
      (p := p) (J := J) (δ := δ) g hg n).mapHomologicalComplex (.up ℕ)).map a)) :
    IsIso (((Subsite.restriction
      (p := p) (J := J) (δ := δ) fY g.opensRange.ι n).mapHomologicalComplex (.up ℕ)).map a) := by
  let : IsIso (((Sheaves.equivalence g hg n).functor.mapHomologicalComplex (.up ℕ)).map
      (((Subsite.restriction fY g n).mapHomologicalComplex (.up ℕ)).map a)) := h
  have h' := isIso_of_reflects_iso
    (((Subsite.restriction fY g n).mapHomologicalComplex (.up ℕ)).map a)
    ((Sheaves.equivalence g hg n).functor.mapHomologicalComplex (.up ℕ))
  have heq := property_eq (p := p) (J := J) (δ := δ) (fY := fY) g n
  let : (Subsite.property (p := p) (J := J) (δ := δ) fY g n).ι.IsContinuous
      ((Subsite.property (p := p) (J := J) (δ := δ) fY g n).ι.restrictedTopology
        (BoundedCrystalline.Site.topology fY n)) (BoundedCrystalline.Site.topology fY n) :=
    Subsite.continuous fY g n
  let : (Subsite.property (p := p) (J := J) (δ := δ) fY g.opensRange.ι n).ι.IsContinuous
      ((Subsite.property (p := p) (J := J) (δ := δ) fY g.opensRange.ι n).ι.restrictedTopology
        (BoundedCrystalline.Site.topology fY n)) (BoundedCrystalline.Site.topology fY n) :=
    Subsite.continuous fY g.opensRange.ι n
  exact isIso_congr n a _ _ heq h'

theorem quasiIso
    (h : QuasiIso (((Bounded.PostcomposeTopology.restriction
      (p := p) (J := J) (δ := δ) g hg n).mapHomologicalComplex (.up ℕ)).map a)) :
    QuasiIso (((Subsite.restriction
      (p := p) (J := J) (δ := δ) fY g.opensRange.ι n).mapHomologicalComplex (.up ℕ)).map a) := by
  have h' := (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (((Subsite.restriction fY g n).mapHomologicalComplex (.up ℕ)).map a)
    (Sheaves.equivalence g hg n).functor).mp h
  have heq := property_eq (p := p) (J := J) (δ := δ) (fY := fY) g n
  let : (Subsite.property (p := p) (J := J) (δ := δ) fY g n).ι.IsContinuous
      ((Subsite.property (p := p) (J := J) (δ := δ) fY g n).ι.restrictedTopology
        (BoundedCrystalline.Site.topology fY n)) (BoundedCrystalline.Site.topology fY n) :=
    Subsite.continuous fY g n
  let : (Subsite.property (p := p) (J := J) (δ := δ) fY g.opensRange.ι n).ι.IsContinuous
      ((Subsite.property (p := p) (J := J) (δ := δ) fY g.opensRange.ι n).ι.restrictedTopology
        (BoundedCrystalline.Site.topology fY n)) (BoundedCrystalline.Site.topology fY n) :=
    Subsite.continuous fY g.opensRange.ι n
  exact quasiIso_congr n a _ _ heq h'

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.ImageRestriction
