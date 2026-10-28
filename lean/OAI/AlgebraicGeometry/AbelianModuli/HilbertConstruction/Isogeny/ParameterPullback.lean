import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.TargetTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterLevelPointComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismCompositionLaws
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Multiplication.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.GroupDivisionLocus

/-! # Parameter Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.ParameterPullback

noncomputable section

/-! Isogenies restricted along a parameter map remain on the original
single pullbacks. Their full kernel type and actual division equation
are preserved by the canonical family comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem isogeny_eq_of_hom_eq
    {S : Scheme.{u}} {g h : ℕ} {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme h S}
    {p q : Abelian.Schemes.AbelianScheme.Isogeny A B} (he : p.hom = q.hom) : p = q := by
  cases p
  cases q
  cases he
  rfl

def isogenyParameterPullback
    {S : Scheme.{u}} {g h : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    {U T : Over S} (p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) (B.pullback T.hom))
    (c : U ⟶ T) : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback U.hom) (B.pullback U.hom) :=
  ((p.pullback c.left).familyTransport (A.parameterPullbackIso c).symm).targetTransport
    (B.parameterPullbackIso c).symm

theorem isogenyParameterPullback_hom
    {S : Scheme.{u}} {g h : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    {U T : Over S} (p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) (B.pullback T.hom))
    (c : U ⟶ T) :
    (isogenyParameterPullback A B p c).hom = Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c p.hom := by
  change ((A.parameterPullbackIso c).hom ≫ (Over.pullback c.left).map p.hom) ≫
    (B.parameterPullbackIso c).inv =
      (A.parameterPullbackIso c).hom ≫ (Over.pullback c.left).map p.hom ≫
        (B.parameterPullbackIso c).inv
  exact Category.assoc _ _ _

theorem isogenyParameterPullback_hasType_iff
    {S : Scheme.{u}} {g : ℕ} (A B : Abelian.Schemes.AbelianScheme g S)
    {U T : Over S} (p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) (B.pullback T.hom))
    (c : U ⟶ T) (δ : Fin g → ℕ) :
    (isogenyParameterPullback A B p c).HasPolarizationType δ ↔
      (p.pullback c.left).HasPolarizationType δ := by
  let eA : (A.pullback U.hom).scheme ≅ ((A.pullback T.hom).pullback c.left).scheme :=
    A.parameterPullbackIso c
  let eB : (B.pullback U.hom).scheme ≅ ((B.pullback T.hom).pullback c.left).scheme :=
    B.parameterPullbackIso c
  let k : ((A.pullback T.hom).pullback c.left).scheme ⟶
      ((B.pullback T.hom).pullback c.left).scheme := (p.pullback c.left).hom
  constructor
  · intro hp
    have he : ((isogenyParameterPullback A B p c).targetTransport eB).familyTransport eA =
        p.pullback c.left := by
      apply isogeny_eq_of_hom_eq
      change eA.inv ≫ (((eA.hom ≫ k) ≫ eB.inv) ≫ eB.hom) = k
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
    exact he ▸ (hp.targetTransport eB).familyTransport eA
  · intro hp
    exact (hp.familyTransport eA.symm).targetTransport eB.symm

theorem isogenyParameterPullback_division
    {S : Scheme.{u}} {g h : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    {U T : Over S} (p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) (B.pullback T.hom))
    (c : U ⟶ T) (n : ℕ) (m : A.scheme ⟶ B.scheme)
    (hp : (A.pullback T.hom).multiplication n ≫ p.hom = (Over.pullback T.hom).map m) :
    (A.pullback U.hom).multiplication n ≫ (isogenyParameterPullback A B p c).hom =
      (Over.pullback U.hom).map m := by
  let a : (Over.pullback T.hom).obj A.scheme ⟶ (Over.pullback T.hom).obj A.scheme :=
    (A.pullback T.hom).multiplication n
  let z : (Over.pullback T.hom).obj A.scheme ⟶ (Over.pullback T.hom).obj B.scheme := p.hom
  let aU : (Over.pullback U.hom).obj A.scheme ⟶ (Over.pullback U.hom).obj A.scheme :=
    (A.pullback U.hom).multiplication n
  let pU : (Over.pullback U.hom).obj A.scheme ⟶ (Over.pullback U.hom).obj B.scheme :=
    (isogenyParameterPullback A B p c).hom
  let F := Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange (A := A.scheme) (B := B.scheme) c
  let FA := Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange (A := A.scheme) (B := A.scheme) c
  have hbase : (Over.pullback T.hom).map (A.multiplication n) = a :=
    A.multiplication_baseChange T.hom n
  have hmul : FA a = aU :=
    (congrArg FA hbase.symm).trans
      ((Geometric.MorphismCompositionLaws.geometricFamilyMorphismBaseChange_original c (A.multiplication n)).trans
        (A.multiplication_baseChange U.hom n))
  have hz : F z = pU := (isogenyParameterPullback_hom A B p c).symm
  have hcomp : F (a ≫ z) = FA a ≫ F z :=
    Geometric.MorphismCompositionLaws.geometricFamilyMorphismBaseChange_map_comp c a z
  have hp0 : a ≫ z = (Over.pullback T.hom).map m := hp
  have hm : F ((Over.pullback T.hom).map m) = (Over.pullback U.hom).map m :=
    Geometric.MorphismCompositionLaws.geometricFamilyMorphismBaseChange_original c m
  exact (congrArg₂ (fun (f : (Over.pullback U.hom).obj A.scheme ⟶
      (Over.pullback U.hom).obj A.scheme)
      (k : (Over.pullback U.hom).obj A.scheme ⟶ (Over.pullback U.hom).obj B.scheme) => f ≫ k)
      hmul.symm hz.symm).trans (hcomp.symm.trans ((congrArg F hp0).trans hm))

theorem isogenyParameterPullback_etale
    {S : Scheme.{u}} {g h : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    {U T : Over S} (p : Abelian.Schemes.AbelianScheme.Isogeny (A.pullback T.hom) (B.pullback T.hom))
    [Etale p.hom.left] (c : U ⟶ T) :
    Etale (isogenyParameterPullback A B p c).hom.left := by
  let k := p.pullback c.left
  let : Etale k.hom.left :=
    MorphismProperty.overPullbackMap c.left p.hom (inferInstance : Etale p.hom.left)
  let : IsIso (A.parameterPullbackIso c).hom.left :=
    inferInstanceAs (IsIso ((Over.forget U.left).map (A.parameterPullbackIso c).hom))
  let : IsIso (B.parameterPullbackIso c).inv.left :=
    inferInstanceAs (IsIso ((Over.forget U.left).map (B.parameterPullbackIso c).inv))
  change Etale (((A.parameterPullbackIso c).hom.left ≫ k.hom.left) ≫
    (B.parameterPullbackIso c).inv.left)
  infer_instance

theorem rational_divisor_unique
    {S : Scheme} (qS : S ⟶ Spec (.of ℚ)) {g h : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S) (n : ℕ) (hn : 0 < n)
    {m p q : A.scheme ⟶ B.scheme}
    (hp : A.multiplication n ≫ p = m) (hq : A.multiplication n ≫ q = m) : p = q := by
  have hg := Rational.GroupDivisionLocus.rational_multiplication_geometry qS A n hn
  let : IsFinite (A.multiplication n).left := hg.1
  let : Flat (A.multiplication n).left := hg.2.1
  let : Surjective (A.multiplication n).left := hg.2.2.1
  let : EffectiveEpi (A.multiplication n).left := inferInstance
  let : Epi (A.multiplication n) := Over.epi_of_epi_left _
  exact (cancel_epi (A.multiplication n)).mp (hp.trans hq.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.ParameterPullback
