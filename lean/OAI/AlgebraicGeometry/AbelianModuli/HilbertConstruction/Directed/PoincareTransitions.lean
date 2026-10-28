import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedSchemeGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RigidifiedLineCanonicalComparisons
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareFixedComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.PoincareTotalMap

/-! # Poincare Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PoincareTransitions.DirectedPolarizedSchemeGluing

noncomputable section

/-! The original local Poincare bundles on the already glued abelian
family. Their transition compatibility follows from the original
polarized isomorphisms and the actual colimit triangles. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

private theorem postcompose_commuting_square
    {B : Type*} [Category* B] {W X Y Z T : B}
    (q : W ⟶ X) (x : X ⟶ Y) (w : W ⟶ Z) (d : Z ⟶ Y)
    (a : Y ⟶ T) (b : Z ⟶ T)
    (h : q ≫ x = w ≫ d) (k : d ≫ a = b) :
    q ≫ (x ≫ a) = w ≫ b := by
  rw [← Category.assoc, h, Category.assoc, k]

private theorem comparison_first_projection
    {B : Type*} [Category* B] {P Q U V I J : B}
    (ci : P ⟶ U) (cj : Q ⟶ V) (t : U ⟶ V) (q : P ⟶ Q)
    (pi : U ⟶ I) (pj : V ⟶ J) (ri : P ⟶ I) (rj : Q ⟶ J) (d : I ⟶ J)
    (ht : t ≫ pj = pi ≫ d) (hi : ci ≫ pi = ri)
    (hj : cj ≫ pj = rj) (hq : q ≫ rj = ri ≫ d) :
    (ci ≫ t) ≫ pj = (q ≫ cj) ≫ pj := by
  calc
    (ci ≫ t) ≫ pj = ci ≫ (t ≫ pj) := Category.assoc _ _ _
    _ = ci ≫ (pi ≫ d) := congrArg (fun x => ci ≫ x) ht
    _ = (ci ≫ pi) ≫ d := (Category.assoc _ _ _).symm
    _ = ri ≫ d := congrArg (fun x => x ≫ d) hi
    _ = q ≫ rj := hq.symm
    _ = q ≫ (cj ≫ pj) := congrArg (fun x => q ≫ x) hj.symm
    _ = (q ≫ cj) ≫ pj := (Category.assoc _ _ _).symm

private theorem comparison_second_projection
    {B : Type*} [Category* B] {P Q U V I J Z : B}
    (ci : P ⟶ U) (cj : Q ⟶ V) (t : U ⟶ V) (q : P ⟶ Q)
    (pi : U ⟶ Z) (pj : V ⟶ Z) (ri : P ⟶ I) (rj : Q ⟶ J)
    (ai : I ⟶ Z) (aj : J ⟶ Z) (u : I ⟶ J)
    (ht : t ≫ pj = pi) (hi : ci ≫ pi = ri ≫ ai)
    (hj : cj ≫ pj = rj ≫ aj) (hq : q ≫ rj = ri ≫ u) (hu : u ≫ aj = ai) :
    (ci ≫ t) ≫ pj = (q ≫ cj) ≫ pj := by
  calc
    (ci ≫ t) ≫ pj = ci ≫ (t ≫ pj) := Category.assoc _ _ _
    _ = ci ≫ pi := congrArg (fun x => ci ≫ x) ht
    _ = ri ≫ ai := hi
    _ = q ≫ (rj ≫ aj) := (postcompose_commuting_square q rj ri u aj ai hq hu).symm
    _ = q ≫ (cj ≫ pj) := congrArg (fun x => q ≫ x) hj.symm
    _ = (q ≫ cj) ≫ pj := (Category.assoc _ _ _).symm

variable {S : Scheme.{0}} [IsLocallyNoetherian S] (C : S.OpenCover.{0})
  [Category C.I₀] [C.LocallyDirected] [Small.{0} C.I₀] [Quiver.IsThin C.I₀]
  [∀ i, IsLocallyNoetherian (C.X i)] {g N : ℕ} {δ : Fin g → ℕ}
  (F : ∀ i, PolarizationData.PolarizedAbelianWithFullLevel g δ N (C.X i)) (hN : 3 ≤ N)
  (e : ∀ {i j : C.I₀} (f : i ⟶ j), Moduli.Isomorphisms.LevelPreservingIso (F i) ((F j).pullback (C.trans f)))

local notation "A" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelian C F hN e
local notation "DA" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianData C F hN e
local notation "DE" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualData C F hN e

abbrev poincareParameter (i : C.I₀) : Over S := (Over.map (C.f i)).obj (F i).dual.abelian.scheme

def poincareParameterInclusion (i : C.I₀) : poincareParameter C F i ⟶ (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualAbelian C F hN e).scheme :=
  Over.homMk ((DE).chartMap i) ((DE).chartMap_over i)

instance poincareParameterInclusion_open (i : C.I₀) :
    IsOpenImmersion (poincareParameterInclusion C F hN e i).left := (DE).chartMap_open i

def poincareParameterTransition {i j : C.I₀} (f : i ⟶ j) :
    poincareParameter C F i ⟶ poincareParameter C F j :=
  Over.homMk ((DE).transition f)
    (postcompose_commuting_square ((DE).transition f)
      (F j).dual.abelian.scheme.hom (F i).dual.abelian.scheme.hom
      (C.trans f) (C.f j) (C.f i) ((DE).cartesian f).w (C.trans_map f))

omit [IsLocallyNoetherian S] in
theorem poincareParameterTransition_inclusion {i j : C.I₀} (f : i ⟶ j) :
    poincareParameterTransition C F hN e f ≫ poincareParameterInclusion C F hN e j =
      poincareParameterInclusion C F hN e i := by
  apply Over.OverMorphism.ext
  exact (DE).chartMap_transition f

omit [IsLocallyNoetherian S] [Small.{0} C.I₀] [Quiver.IsThin C.I₀] in
theorem poincareParameterTransition_id (i : C.I₀) :
    poincareParameterTransition C F hN e (𝟙 i) = 𝟙 (poincareParameter C F i) := by
  apply Over.OverMorphism.ext
  exact (DE).transition_id i

omit [IsLocallyNoetherian S] [Small.{0} C.I₀] [Quiver.IsThin C.I₀] in
theorem poincareParameterTransition_comp {i j k : C.I₀} (f : i ⟶ j) (h : j ⟶ k) :
    poincareParameterTransition C F hN e (f ≫ h) =
      poincareParameterTransition C F hN e f ≫ poincareParameterTransition C F hN e h := by
  apply Over.OverMorphism.ext
  exact (DE).transition_comp f h

/-- Each local line is the original Poincare line transported only in
its abelian factor. The parameter remains the original local dual. -/
def localPoincare (i : C.I₀) : Line.Bundles.LineBundle (poincareParameter C F i ⊗ (A).scheme).left :=
  ReferenceFamily.PoincareFixed.fixedFamilyPoincare (F i).dual A (C.f i) (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i)

def localPoincareZero (i : C.I₀) :
    ((localPoincare C F hN e i).pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A (poincareParameter C F i)).left).sheaf ≅
      Line.Bundles.structureModule (poincareParameter C F i).left :=
  ReferenceFamily.PoincareFixed.fixedFamilyPoincare_zeroIso (F i).dual A (C.f i) (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i)

omit [IsLocallyNoetherian S] in
theorem localPoincare_homogeneous (i : C.I₀) :
    (A).IsHomogeneousPicardClass (poincareParameter C F i) (Line.Bundles.LineBundle.classOf (localPoincare C F hN e i)) :=
  ReferenceFamily.PoincareFixed.fixedFamilyPoincare_homogeneous (F i).dual A (C.f i) (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i)

def localPoincareRigidified (i : C.I₀) : RigidifiedLineBundles.RigidifiedLineBundle (Isogenies.NeighborCounting.PoincareNormalization.familyZero A (poincareParameter C F i)).left :=
  ⟨localPoincare C F hN e i, localPoincareZero C F hN e i⟩

def localPoincareComparison (i : C.I₀) :
    ((F i).dual.abelian.scheme ⊗ (F i).abelian.scheme).left ≅
      (poincareParameter C F i ⊗ (A).scheme).left :=
  ReferenceFamily.PoincareFixedComparison.fixedFamilyPoincareComparison (F i).dual A (C.f i) (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i)

omit [IsLocallyNoetherian S] in
theorem localPoincareComparison_transition {i j : C.I₀} (f : i ⟶ j) :
    (localPoincareComparison C F hN e i).hom ≫
        (poincareParameterTransition C F hN e f ▷ (A).scheme).left =
      ReferenceFamily.Polarized.PoincareTotalMap.polarizedPoincareTotalMap (F j) (F i) (C.trans f) (e f) ≫
        (localPoincareComparison C F hN e j).hom := by
  let ci := localPoincareComparison C F hN e i
  let cj := localPoincareComparison C F hN e j
  let t := poincareParameterTransition C F hN e f
  let q := ReferenceFamily.Polarized.PoincareTotalMap.polarizedPoincareTotalMap (F j) (F i) (C.trans f) (e f)
  let ai := ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap (C.f i) (F i).abelian.scheme (A).scheme
    (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i)
  let aj := ReferenceFamily.CartesianFiberComparison.CartesianFamily.totalMap (C.f j) (F j).abelian.scheme (A).scheme
    (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e j)
  have hai : ai = (DA).chartMap i := (DA).chartIso_fst i
  have haj : aj = (DA).chartMap j := (DA).chartIso_fst j
  let u : (F i).abelian.scheme.left ⟶ (F j).abelian.scheme.left :=
    ReferenceFamily.Polarized.TotalMaps.polarizedTotalMap (F j) (F i) (C.trans f) (e f)
  have hchart : u ≫ (DA).chartMap j = (DA).chartMap i := (DA).chartMap_transition f
  have hta : u ≫ aj = ai :=
    (congrArg (fun m : (F j).abelian.scheme.left ⟶ (A).scheme.left => u ≫ m) haj).trans
      (hchart.trans hai.symm)
  have hci₁ : ci.hom ≫ (fst (poincareParameter C F i) (A).scheme).left =
      (fst (F i).dual.abelian.scheme (F i).abelian.scheme).left :=
    ReferenceFamily.PoincareFixedComparison.fixedFamilyPoincareComparison_fst (F i).dual A (C.f i) (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i)
  have hcj₁ : cj.hom ≫ (fst (poincareParameter C F j) (A).scheme).left =
      (fst (F j).dual.abelian.scheme (F j).abelian.scheme).left :=
    ReferenceFamily.PoincareFixedComparison.fixedFamilyPoincareComparison_fst (F j).dual A (C.f j) (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e j)
  have hci₂ : ci.hom ≫ (snd (poincareParameter C F i) (A).scheme).left =
      (snd (F i).dual.abelian.scheme (F i).abelian.scheme).left ≫ ai :=
    ReferenceFamily.PoincareFixedComparison.fixedFamilyPoincareComparison_snd (F i).dual A (C.f i) (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i)
  have hcj₂ : cj.hom ≫ (snd (poincareParameter C F j) (A).scheme).left =
      (snd (F j).dual.abelian.scheme (F j).abelian.scheme).left ≫ aj :=
    ReferenceFamily.PoincareFixedComparison.fixedFamilyPoincareComparison_snd (F j).dual A (C.f j) (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e j)
  have hq₁ : q ≫ (fst (F j).dual.abelian.scheme (F j).abelian.scheme).left =
      (fst (F i).dual.abelian.scheme (F i).abelian.scheme).left ≫ t.left :=
    ReferenceFamily.Polarized.PoincareTotalMap.polarizedPoincareTotalMap_fst (F j) (F i) (C.trans f) (e f)
  have hq₂ : q ≫ (snd (F j).dual.abelian.scheme (F j).abelian.scheme).left =
      (snd (F i).dual.abelian.scheme (F i).abelian.scheme).left ≫ u :=
    ReferenceFamily.Polarized.PoincareTotalMap.polarizedPoincareTotalMap_snd (F j) (F i) (C.trans f) (e f)
  have ht₁ : (t ▷ (A).scheme).left ≫ (fst (poincareParameter C F j) (A).scheme).left =
      (fst (poincareParameter C F i) (A).scheme).left ≫ t.left :=
    congrArg Over.Hom.left (whiskerRight_fst t (A).scheme)
  have ht₂ : (t ▷ (A).scheme).left ≫ (snd (poincareParameter C F j) (A).scheme).left =
      (snd (poincareParameter C F i) (A).scheme).left :=
    congrArg Over.Hom.left (whiskerRight_snd t (A).scheme)
  change ci.hom ≫ (t ▷ (A).scheme).left = q ≫ cj.hom
  apply Over.tensorObj_ext
  · exact comparison_first_projection ci.hom cj.hom (t ▷ (A).scheme).left q
      (fst (poincareParameter C F i) (A).scheme).left
      (fst (poincareParameter C F j) (A).scheme).left
      (fst (F i).dual.abelian.scheme (F i).abelian.scheme).left
      (fst (F j).dual.abelian.scheme (F j).abelian.scheme).left t.left ht₁ hci₁ hcj₁ hq₁
  · exact comparison_second_projection ci.hom cj.hom (t ▷ (A).scheme).left q
      (snd (poincareParameter C F i) (A).scheme).left
      (snd (poincareParameter C F j) (A).scheme).left
      (snd (F i).dual.abelian.scheme (F i).abelian.scheme).left
      (snd (F j).dual.abelian.scheme (F j).abelian.scheme).left ai aj u ht₂ hci₂ hcj₂ hq₂ hta

omit [IsLocallyNoetherian S] in
theorem localPoincare_transition_class {i j : C.I₀} (f : i ⟶ j) :
    Line.Bundles.LineBundle.pullbackClass (poincareParameterTransition C F hN e f ▷ (A).scheme).left
      (Line.Bundles.LineBundle.classOf (localPoincare C F hN e j)) =
      Line.Bundles.LineBundle.classOf (localPoincare C F hN e i) := by
  let ci := localPoincareComparison C F hN e i
  let cj := localPoincareComparison C F hN e j
  let t := (poincareParameterTransition C F hN e f ▷ (A).scheme).left
  let q := ReferenceFamily.Polarized.PoincareTotalMap.polarizedPoincareTotalMap (F j) (F i) (C.trans f) (e f)
  let Li := Line.Bundles.LineBundle.classOf (localPoincare C F hN e i)
  let Lj := Line.Bundles.LineBundle.classOf (localPoincare C F hN e j)
  have hi : Line.Bundles.LineBundle.pullbackClass ci.hom Li = Line.Bundles.LineBundle.classOf (F i).dual.poincare :=
    ReferenceFamily.PoincareFixedComparison.fixedFamilyPoincare_recovery_class (F i).dual A (C.f i) (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i)
  have hj : Line.Bundles.LineBundle.pullbackClass cj.hom Lj = Line.Bundles.LineBundle.classOf (F j).dual.poincare :=
    ReferenceFamily.PoincareFixedComparison.fixedFamilyPoincare_recovery_class (F j).dual A (C.f j) (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e j)
  apply (Line.Bundles.LineBundle.pullbackIso ci).injective
  change Line.Bundles.LineBundle.pullbackClass ci.hom (Line.Bundles.LineBundle.pullbackClass t Lj) = Line.Bundles.LineBundle.pullbackClass ci.hom Li
  exact (Line.Bundles.LineBundle.pullbackClass_comp ci.hom t Lj).symm.trans
    ((congrArg (fun m => Line.Bundles.LineBundle.pullbackClass m Lj) (localPoincareComparison_transition C F hN e f)).trans
      ((Line.Bundles.LineBundle.pullbackClass_comp q cj.hom Lj).trans
        ((congrArg (Line.Bundles.LineBundle.pullbackClass q) hj).trans
          ((ReferenceFamily.Polarized.PoincareTotalMap.polarizedPoincareTotalMap_class (F j) (F i) (C.trans f) (e f)).trans hi.symm))))

/-- The local transition has its unique actual representative preserving
both chosen zero frames. -/
def localPoincareTransitionIso {i j : C.I₀} (f : i ⟶ j) :
    RigidifiedLineBundles.RigidifiedLineBundleIso
      ((localPoincareRigidified C F hN e j).pullbackSquare
        (poincareParameterTransition C F hN e f ▷ (A).scheme).left
        (Isogenies.NeighborCounting.PoincareNormalization.familyZero A (poincareParameter C F i)).left
        (poincareParameterTransition C F hN e f).left
        (congrArg Over.Hom.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_naturality A (poincareParameterTransition C F hN e f))))
      (localPoincareRigidified C F hN e i) :=
  (A).rigidifiedProductComparison (poincareParameter C F i) _ _
    (Quotient.exact (s := Line.Bundles.LineBundle.isoSetoid _)
      (a := (localPoincare C F hN e j).pullback
        (poincareParameterTransition C F hN e f ▷ (A).scheme).left)
      (b := localPoincare C F hN e i) (localPoincare_transition_class C F hN e f))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PoincareTransitions.DirectedPolarizedSchemeGluing
