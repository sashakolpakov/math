import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedSchemeGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.OpenDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.TargetTransport

/-! # Polarization Isogeny Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizationIsogenyGluing.DirectedPolarizedSchemeGluing

noncomputable section

/-! The original polarization arrows glue between the two effectively
glued abelian schemes. Their finite-flat isogeny structure and full kernel
type are retained, before constructing the global Poincare line. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private theorem polarization_total_square {C : Type*} [Category* C]
    {X Y X' Y' U V : C} (a : X ⟶ X') (b : Y ⟶ Y') (p : X ⟶ Y) (q : X' ⟶ Y')
    (r : X' ⟶ U) (s : Y' ⟶ V) (h : U ⟶ V)
    (hp : p ≫ b = a ≫ q) (hq : q ≫ s = r ≫ h) :
    (a ≫ r) ≫ h = p ≫ (b ≫ s) := by
  rw [Category.assoc, ← hq, ← Category.assoc, ← hp, Category.assoc]

private theorem polarization_cocone_square {C : Type*} [Category* C]
    {X Y X' Y' Z : C} (a : X ⟶ X') (b : Y ⟶ Y') (p : X ⟶ Y) (q : X' ⟶ Y')
    (i : Y ⟶ Z) (j : Y' ⟶ Z) (hp : a ≫ q = p ≫ b) (hb : b ≫ j = i) :
    a ≫ (q ≫ j) = (p ≫ i) ≫ 𝟙 Z := by
  rw [← Category.assoc, hp, Category.assoc, hb, Category.comp_id]

private theorem polarization_base_square {C : Type*} [Category* C]
    {X Y U V T S : C} (a : X ⟶ U) (b : Y ⟶ V) (p : X ⟶ Y) (q : U ⟶ V)
    (u : U ⟶ S) (v : V ⟶ S) (x : X ⟶ T) (y : Y ⟶ T) (t : T ⟶ S)
    (hp : a ≫ q = p ≫ b) (hb : b ≫ v = y ≫ t) (hxy : p ≫ y = x)
    (ha : a ≫ u = x ≫ t) : a ≫ (q ≫ v) = a ≫ u := by
  calc
    a ≫ (q ≫ v) = (a ≫ q) ≫ v := (Category.assoc _ _ _).symm
    _ = (p ≫ b) ≫ v := congrArg (fun f => f ≫ v) hp
    _ = p ≫ (b ≫ v) := Category.assoc _ _ _
    _ = p ≫ (y ≫ t) := congrArg (fun f => p ≫ f) hb
    _ = (p ≫ y) ≫ t := (Category.assoc _ _ _).symm
    _ = x ≫ t := congrArg (fun f => f ≫ t) hxy
    _ = a ≫ u := ha.symm

private theorem polarization_first_projection {C : Type*} [Category* C]
    {X Y U V G H : C} (a : X ⟶ U) (b : Y ⟶ V) (p : X ⟶ Y) (q : U ⟶ V)
    (u : U ⟶ G) (v : V ⟶ H) (i : X ⟶ G) (j : Y ⟶ H) (w : G ⟶ H)
    (ha : a ≫ u = i) (hb : b ≫ v = j) (hq : q ≫ v = u ≫ w)
    (hw : i ≫ w = p ≫ j) : (a ≫ q) ≫ v = (p ≫ b) ≫ v := by
  rw [Category.assoc, hq, ← Category.assoc, ha, hw, Category.assoc, hb]

private theorem polarization_solve_square {C : Type*} [Category* C]
    {X Y U V : C} (a : X ≅ U) (p : X ⟶ Y) (b : Y ⟶ V) (q : U ⟶ V)
    (h : a.hom ≫ q = p ≫ b) : q = (a.inv ≫ p) ≫ b := by
  calc
    q = a.inv ≫ (a.hom ≫ q) := by rw [a.inv_hom_id_assoc]
    _ = a.inv ≫ (p ≫ b) := congrArg (fun f => a.inv ≫ f) h
    _ = (a.inv ≫ p) ≫ b := (Category.assoc _ _ _).symm

variable {S : Scheme.{u}} (C : S.OpenCover.{u})
  [Category C.I₀] [C.LocallyDirected] [Small.{u} C.I₀] [Quiver.IsThin C.I₀]
  [∀ i, IsLocallyNoetherian (C.X i)] {g N : ℕ} {δ : Fin g → ℕ}
  (F : ∀ i, PolarizationData.PolarizedAbelianWithFullLevel g δ N (C.X i)) (hN : 3 ≤ N)
  (e : ∀ {i j : C.I₀} (f : i ⟶ j), Moduli.Isomorphisms.LevelPreservingIso (F i) ((F j).pullback (C.trans f)))

local notation "DA" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianData C F hN e
local notation "DB" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualData C F hN e
local notation "A" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelian C F hN e
local notation "B" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualAbelian C F hN e

omit [Small.{u, u} C.I₀] [Quiver.IsThin C.I₀] in
theorem polarizationTotal_natural {i j : C.I₀} (f : i ⟶ j) :
    (DA).transition f ≫ (F j).polarization.isogeny.hom.left =
      (F i).polarization.isogeny.hom.left ≫ (DB).transition f := by
  let a : (F i).abelian.scheme.left ⟶ pullback (F j).abelian.scheme.hom (C.trans f) :=
    (e f).abelian.hom.left
  let b : (F i).dual.abelian.scheme.left ⟶ pullback (F j).dual.abelian.scheme.hom (C.trans f) :=
    (e f).dual.hom.left
  let q : pullback (F j).abelian.scheme.hom (C.trans f) ⟶
      pullback (F j).dual.abelian.scheme.hom (C.trans f) :=
    ((Over.pullback (C.trans f)).map (F j).polarization.isogeny.hom).left
  have hp : (F i).polarization.isogeny.hom.left ≫ b = a ≫ q :=
    congrArg Over.Hom.left (e f).polarization
  exact polarization_total_square a b (F i).polarization.isogeny.hom.left q
    (pullback.fst (F j).abelian.scheme.hom (C.trans f))
    (pullback.fst (F j).dual.abelian.scheme.hom (C.trans f))
    (F j).polarization.isogeny.hom.left hp
    (Pullback.Comparisons.overPullback_map_left_fst (F j).polarization.isogeny.hom (C.trans f))

def polarizationCocone : Cocone (DA).schemeData.functor where
  pt := (B).scheme.left
  ι :=
    { app i := (F i).polarization.isogeny.hom.left ≫ (DB).chartMap i
      naturality i j f := by
        let a : (F i).abelian.scheme.left ⟶ (F j).abelian.scheme.left := (DA).transition f
        let b : (F i).dual.abelian.scheme.left ⟶ (F j).dual.abelian.scheme.left := (DB).transition f
        let ci : (F i).dual.abelian.scheme.left ⟶ (B).scheme.left := (DB).chartMap i
        let cj : (F j).dual.abelian.scheme.left ⟶ (B).scheme.left := (DB).chartMap j
        exact polarization_cocone_square a b (F i).polarization.isogeny.hom.left
          (F j).polarization.isogeny.hom.left ci cj
          (polarizationTotal_natural C F hN e f) ((DB).chartMap_transition f) }

def polarizationSchemeMap : (A).scheme.left ⟶ (B).scheme.left :=
  colimit.desc (DA).schemeData.functor (polarizationCocone C F hN e)

theorem polarizationSchemeMap_chart (i : C.I₀) :
    (DA).chartMap i ≫ polarizationSchemeMap C F hN e =
      (F i).polarization.isogeny.hom.left ≫ (DB).chartMap i :=
  colimit.ι_desc (F := (DA).schemeData.functor) (polarizationCocone C F hN e) i

def polarizationMap : (A).scheme ⟶ (B).scheme :=
  Over.homMk (polarizationSchemeMap C F hN e) (by
    apply colimit.hom_ext (F := (DA).schemeData.functor)
    intro i
    let a : (F i).abelian.scheme.left ⟶ (A).scheme.left := (DA).chartMap i
    let b : (F i).dual.abelian.scheme.left ⟶ (B).scheme.left := (DB).chartMap i
    exact polarization_base_square a b (F i).polarization.isogeny.hom.left
      (polarizationSchemeMap C F hN e) (A).scheme.hom (B).scheme.hom
      (F i).abelian.scheme.hom (F i).dual.abelian.scheme.hom (C.f i)
      (polarizationSchemeMap_chart C F hN e i) ((DB).chartMap_over i)
      (F i).polarization.isogeny.hom.w ((DA).chartMap_over i))

theorem polarizationMap_chart (i : C.I₀) :
    (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i).hom ≫ (Over.pullback (C.f i)).map (polarizationMap C F hN e) =
      (F i).polarization.isogeny.hom ≫ (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualChartIso C F hN e i).hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · let a : (F i).abelian.scheme.left ⟶ pullback (A).scheme.hom (C.f i) :=
      (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i).hom.left
    let b : (F i).dual.abelian.scheme.left ⟶ pullback (B).scheme.hom (C.f i) :=
      (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualChartIso C F hN e i).hom.left
    let q : pullback (A).scheme.hom (C.f i) ⟶ pullback (B).scheme.hom (C.f i) :=
      ((Over.pullback (C.f i)).map (polarizationMap C F hN e)).left
    let ci : (F i).abelian.scheme.left ⟶ (A).scheme.left := (DA).chartMap i
    let cj : (F i).dual.abelian.scheme.left ⟶ (B).scheme.left := (DB).chartMap i
    exact polarization_first_projection a b (F i).polarization.isogeny.hom.left q
      (pullback.fst (A).scheme.hom (C.f i)) (pullback.fst (B).scheme.hom (C.f i))
      ci cj (polarizationSchemeMap C F hN e) ((DA).chartIso_fst i) ((DB).chartIso_fst i)
      (Pullback.Comparisons.overPullback_map_left_fst (polarizationMap C F hN e) (C.f i))
      (polarizationSchemeMap_chart C F hN e i)
  · exact ((PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i).hom ≫
      (Over.pullback (C.f i)).map (polarizationMap C F hN e)).w.trans
        ((F i).polarization.isogeny.hom ≫ (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualChartIso C F hN e i).hom).w.symm

def localIsogeny (i : C.I₀) : Abelian.Schemes.AbelianScheme.Isogeny ((A).pullback (C.f i)) ((B).pullback (C.f i)) :=
  ((F i).polarization.isogeny.familyTransport (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i)).targetTransport
    (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualChartIso C F hN e i)

theorem localIsogeny_type (i : C.I₀) : (localIsogeny C F hN e i).HasPolarizationType δ :=
  ((F i).polarization.kernelType.familyTransport (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i)).targetTransport
    (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualChartIso C F hN e i)

theorem polarizationMap_pullback (i : C.I₀) :
    (Over.pullback (C.f i)).map (polarizationMap C F hN e) = (localIsogeny C F hN e i).hom :=
  polarization_solve_square (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i) (F i).polarization.isogeny.hom
    (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualChartIso C F hN e i).hom ((Over.pullback (C.f i)).map (polarizationMap C F hN e))
    (polarizationMap_chart C F hN e i)

def isogeny : Abelian.Schemes.AbelianScheme.Isogeny A B := by
  let p := polarizationMap C F hN e
  let : IsMonHom p := MonoidHomOpenLocality.isMonHom_of_openCover p C (fun i =>
    (polarizationMap_pullback C F hN e i).symm ▸ (localIsogeny C F hN e i).preservesGroup)
  let : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      IsFinite.instHasAffinePropertyAndIsAffineFiniteCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop
  let : IsZariskiLocalAtTarget (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat) (Q := RingHom.Flat)
  exact
    { hom := p
      preservesGroup := inferInstance
      finite := HilbertConstruction.Over.MorphismPropertyOpenDescent.overMorphism_property_of_openCover p C (@IsFinite) (fun i =>
        (congrArg Over.Hom.left (polarizationMap_pullback C F hN e i)).symm ▸
          (localIsogeny C F hN e i).finite)
      flat := HilbertConstruction.Over.MorphismPropertyOpenDescent.overMorphism_property_of_openCover p C (@Flat) (fun i =>
        (congrArg Over.Hom.left (polarizationMap_pullback C F hN e i)).symm ▸
          (localIsogeny C F hN e i).flat)
      surjective := HilbertConstruction.Over.MorphismPropertyOpenDescent.overMorphism_property_of_openCover p C (@Surjective) (fun i =>
        (congrArg Over.Hom.left (polarizationMap_pullback C F hN e i)).symm ▸
          (localIsogeny C F hN e i).surjective) }

theorem isogeny_type : (DirectedPolarizedSchemeGluing.isogeny C F hN e).HasPolarizationType δ := by
  apply Abelian.Schemes.AbelianScheme.Isogeny.hasPolarizationType_of_openCover _ δ C
  intro i
  have he : (DirectedPolarizedSchemeGluing.isogeny C F hN e).pullback (C.f i) = localIsogeny C F hN e i :=
    Isogeny.ParameterPullback.isogeny_eq_of_hom_eq (polarizationMap_pullback C F hN e i)
  exact he.symm ▸ localIsogeny_type C F hN e i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizationIsogenyGluing.DirectedPolarizedSchemeGluing
