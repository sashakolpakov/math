import OAI.AlgebraicGeometry.Albanese.Construction.ProjectiveCover
import OAI.AlgebraicGeometry.Albanese.Construction.SegreCompatibility

/-! # Segre Local -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.SegreLocal

noncomputable section

section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory

abbrev projectivePair (m n : ℕ) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) ⊗ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)

abbrev projectivePairChart (m n : ℕ) (ij : Fin (m + 1) × Fin (n + 1)) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  ProjectiveCover.polynomialChartOver m ij.1 ⊗ ProjectiveCover.polynomialChartOver n ij.2

def projectivePairChartMap (m n : ℕ) (ij : Fin (m + 1) × Fin (n + 1)) :
    projectivePairChart m n ij ⟶ projectivePair m n :=
  ProjectiveCover.polynomialChartOverMap m ij.1 ⊗ₘ ProjectiveCover.polynomialChartOverMap n ij.2

instance projectivePairChart_smooth (m n : ℕ) (ij : Fin (m + 1) × Fin (n + 1)) :
    Smooth (projectivePairChart m n ij).hom := by
  have : Smooth (Foundations.Scheme.ProjectiveChart.projectiveChartPolynomialToBase m ij.1) := ProjectiveCover.polynomialChart_smooth m ij.1
  have : Smooth (Foundations.Scheme.ProjectiveChart.projectiveChartPolynomialToBase n ij.2) := ProjectiveCover.polynomialChart_smooth n ij.2
  dsimp [projectivePairChart]
  infer_instance

instance projectivePairChart_reduced (m n : ℕ) (ij : Fin (m + 1) × Fin (n + 1)) :
    IsReduced (projectivePairChart m n ij).left :=
  Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced (projectivePairChart m n ij).hom

def leftChartTuple {Z : Over Foundations.Scheme.ProjectiveSpace.complexBase} {m n : ℕ} {ij : Fin (m + 1) × Fin (n + 1)}
    (h : Z ⟶ projectivePairChart m n ij) : Fin (m + 1) → Γ(Z.left, ⊤) :=
  fun k => (h ≫ fst _ _).left.appTop (AffineCoordinates.affineChartSections m ij.1 k)

def rightChartTuple {Z : Over Foundations.Scheme.ProjectiveSpace.complexBase} {m n : ℕ} {ij : Fin (m + 1) × Fin (n + 1)}
    (h : Z ⟶ projectivePairChart m n ij) : Fin (n + 1) → Γ(Z.left, ⊤) :=
  fun k => (h ≫ snd _ _).left.appTop (AffineCoordinates.affineChartSections n ij.2 k)

@[simp]
theorem leftChartTuple_normalized {Z : Over Foundations.Scheme.ProjectiveSpace.complexBase} {m n : ℕ}
    {ij : Fin (m + 1) × Fin (n + 1)} (h : Z ⟶ projectivePairChart m n ij) :
    leftChartTuple h ij.1 = 1 := by simp [leftChartTuple]

@[simp]
theorem rightChartTuple_normalized {Z : Over Foundations.Scheme.ProjectiveSpace.complexBase} {m n : ℕ}
    {ij : Fin (m + 1) × Fin (n + 1)} (h : Z ⟶ projectivePairChart m n ij) :
    rightChartTuple h ij.2 = 1 := by simp [rightChartTuple]

set_option backward.isDefEq.respectTransparency false in
theorem leftChartTuple_map {Z : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType Z.hom] [IsReduced Z.left]
    {m n : ℕ} {ij : Fin (m + 1) × Fin (n + 1)} (h : Z ⟶ projectivePairChart m n ij) :
    ProjectiveCoordinates.projectiveMapOfCoordinates Z.hom (leftChartTuple h) ij.1 (leftChartTuple_normalized h) =
      (h ≫ projectivePairChartMap m n ij ≫
        fst (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))).left := by
  have hc : h ≫ projectivePairChartMap m n ij ≫ fst _ _ =
      (h ≫ fst _ _) ≫ ProjectiveCover.polynomialChartOverMap m ij.1 := by simp [projectivePairChartMap]
  rw [hc]
  change _ = (h ≫ fst _ _).left ≫ Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap m ij.1
  rw [← AffineCoordinates.projectiveMapOfCoordinates_affineChart]
  exact (ProjectiveCoordinates.projectiveMapOfCoordinates_comp Z (ProjectiveCover.polynomialChartOver m ij.1) (h ≫ fst _ _)
    (AffineCoordinates.affineChartSections m ij.1) ij.1 (AffineCoordinates.affineChartSections_self m ij.1)).symm

set_option backward.isDefEq.respectTransparency false in
theorem rightChartTuple_map {Z : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType Z.hom] [IsReduced Z.left]
    {m n : ℕ} {ij : Fin (m + 1) × Fin (n + 1)} (h : Z ⟶ projectivePairChart m n ij) :
    ProjectiveCoordinates.projectiveMapOfCoordinates Z.hom (rightChartTuple h) ij.2 (rightChartTuple_normalized h) =
      (h ≫ projectivePairChartMap m n ij ≫
        snd (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))).left := by
  have hc : h ≫ projectivePairChartMap m n ij ≫ snd _ _ =
      (h ≫ snd _ _) ≫ ProjectiveCover.polynomialChartOverMap n ij.2 := by simp [projectivePairChartMap]
  rw [hc]
  change _ = (h ≫ snd _ _).left ≫ Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n ij.2
  rw [← AffineCoordinates.projectiveMapOfCoordinates_affineChart]
  exact (ProjectiveCoordinates.projectiveMapOfCoordinates_comp Z (ProjectiveCover.polynomialChartOver n ij.2) (h ≫ snd _ _)
    (AffineCoordinates.affineChartSections n ij.2) ij.2 (AffineCoordinates.affineChartSections_self n ij.2)).symm

/-- The Segre map on a scheme mapping to a product coordinate chart. -/
def segreAlongChart {Z : Over Foundations.Scheme.ProjectiveSpace.complexBase} {m n : ℕ} {ij : Fin (m + 1) × Fin (n + 1)}
    (h : Z ⟶ projectivePairChart m n ij) : Z ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (SegreCoordinates.segreDimension m n)) :=
  Over.homMk (SegreCoordinates.segreMapOfCoordinates Z.hom (leftChartTuple h) (rightChartTuple h)
    ij.1 ij.2 (leftChartTuple_normalized h) (rightChartTuple_normalized h))
    (SegreCoordinates.segreMapOfCoordinates_over _ _ _ _ _ _ _)

/-- The Segre morphism on one chart of the projective product. -/
def segreChartMap (m n : ℕ) (ij : Fin (m + 1) × Fin (n + 1)) :
    projectivePairChart m n ij ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (SegreCoordinates.segreDimension m n)) :=
  segreAlongChart (𝟙 _)

set_option backward.isDefEq.respectTransparency false in
theorem segreChartMap_comp {Z : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType Z.hom] [IsReduced Z.left]
    {m n : ℕ} {ij : Fin (m + 1) × Fin (n + 1)} (h : Z ⟶ projectivePairChart m n ij) :
    h ≫ segreChartMap m n ij = segreAlongChart h := by
  apply Over.OverMorphism.ext
  change h.left ≫ SegreCoordinates.segreMapOfCoordinates (projectivePairChart m n ij).hom
    (leftChartTuple (𝟙 (projectivePairChart m n ij))) (rightChartTuple (𝟙 (projectivePairChart m n ij)))
    ij.1 ij.2 (leftChartTuple_normalized _) (rightChartTuple_normalized _) =
      SegreCoordinates.segreMapOfCoordinates Z.hom (leftChartTuple h) (rightChartTuple h)
        ij.1 ij.2 (leftChartTuple_normalized h) (rightChartTuple_normalized h)
  rw [SegreCompatibility.segreMapOfCoordinates_comp Z (projectivePairChart m n ij) h]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The local Segre maps agree whenever their maps to the projective product
agree. In particular, they agree on every overlap of the product cover. -/
theorem segreAlongChart_eq {Z : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType Z.hom] [IsReduced Z.left]
    {m n : ℕ} {ij kl : Fin (m + 1) × Fin (n + 1)}
    (h : Z ⟶ projectivePairChart m n ij) (k : Z ⟶ projectivePairChart m n kl)
    (heq : h ≫ projectivePairChartMap m n ij = k ≫ projectivePairChartMap m n kl) :
    segreAlongChart h = segreAlongChart k := by
  apply Over.OverMorphism.ext
  apply SegreCompatibility.segreMapOfCoordinates_eq Z (leftChartTuple h) (leftChartTuple k)
    (rightChartTuple h) (rightChartTuple k) ij.1 kl.1 ij.2 kl.2
    (leftChartTuple_normalized h) (leftChartTuple_normalized k)
    (rightChartTuple_normalized h) (rightChartTuple_normalized k)
  · rw [leftChartTuple_map, leftChartTuple_map]
    have hc := congrArg (fun a : Z ⟶ projectivePair m n =>
      a ≫ fst (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))) heq
    simpa only [Category.assoc] using congrArg Over.Hom.left hc
  · rw [rightChartTuple_map, rightChartTuple_map]
    have hc := congrArg (fun a : Z ⟶ projectivePair m n =>
      a ≫ snd (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))) heq
    simpa only [Category.assoc] using congrArg Over.Hom.left hc

end

section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory

instance projectivePairChartMap_open (m n : ℕ) (ij : Fin (m + 1) × Fin (n + 1)) :
    IsOpenImmersion (projectivePairChartMap m n ij).left :=
  (ProjectiveCover.projectiveProductCover m n).map_prop ij

set_option backward.isDefEq.respectTransparency false in
/-- The local Segre morphisms agree on the actual scheme-theoretic chart
overlaps. Reducedness of these smooth overlaps justifies the point test. -/
theorem segreChartMap_overlap (m n : ℕ) (ij kl : Fin (m + 1) × Fin (n + 1)) :
    pullback.fst (projectivePairChartMap m n ij).left (projectivePairChartMap m n kl).left ≫
        (segreChartMap m n ij).left =
      pullback.snd (projectivePairChartMap m n ij).left (projectivePairChartMap m n kl).left ≫
        (segreChartMap m n kl).left := by
  let c := projectivePairChartMap m n ij
  let d := projectivePairChartMap m n kl
  let Z : Over Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (pullback.fst c.left d.left ≫ (projectivePairChart m n ij).hom)
  have hbase : pullback.snd c.left d.left ≫ (projectivePairChart m n kl).hom = Z.hom := by
    change pullback.snd c.left d.left ≫ (projectivePairChart m n kl).hom =
      pullback.fst c.left d.left ≫ (projectivePairChart m n ij).hom
    rw [← d.w, ← Category.assoc, ← pullback.condition, Category.assoc, c.w]
  let h : Z ⟶ projectivePairChart m n ij := Over.homMk (pullback.fst c.left d.left) rfl
  let k : Z ⟶ projectivePairChart m n kl := Over.homMk (pullback.snd c.left d.left) hbase
  have : IsOpenImmersion c.left := projectivePairChartMap_open m n ij
  have : IsOpenImmersion d.left := projectivePairChartMap_open m n kl
  have : Smooth Z.hom := by
    change Smooth (pullback.fst c.left d.left ≫ (projectivePairChart m n ij).hom)
    infer_instance
  have : IsReduced Z.left := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced Z.hom
  have heq : h ≫ projectivePairChartMap m n ij = k ≫ projectivePairChartMap m n kl := by
    apply Over.OverMorphism.ext
    exact pullback.condition
  have H := (segreChartMap_comp h).trans ((segreAlongChart_eq h k heq).trans (segreChartMap_comp k).symm)
  exact congrArg Over.Hom.left H

/-- The global algebraic Segre morphism, glued from normalized coordinate
products on the genuine finite polynomial-chart cover. -/
def segreMap (m n : ℕ) : (projectivePair m n).left ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace (SegreCoordinates.segreDimension m n) :=
  (ProjectiveCover.projectiveProductCover m n).glueMorphisms (fun ij => (segreChartMap m n ij).left)
    (segreChartMap_overlap m n)

@[reassoc (attr := simp)]
theorem chartMap_segreMap (m n : ℕ) (ij : Fin (m + 1) × Fin (n + 1)) :
    (projectivePairChartMap m n ij).left ≫ segreMap m n = (segreChartMap m n ij).left :=
  (ProjectiveCover.projectiveProductCover m n).ι_glueMorphisms _ _ ij

set_option backward.isDefEq.respectTransparency false in
/-- The glued Segre morphism respects the complex structure map. -/
@[reassoc (attr := simp)]
theorem segreMap_over (m n : ℕ) :
    segreMap m n ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (SegreCoordinates.segreDimension m n) = (projectivePair m n).hom := by
  apply (ProjectiveCover.projectiveProductCover m n).hom_ext
  intro ij
  change (projectivePairChartMap m n ij).left ≫
    (segreMap m n ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (SegreCoordinates.segreDimension m n)) =
      (projectivePairChartMap m n ij).left ≫ (projectivePair m n).hom
  rw [← Category.assoc, chartMap_segreMap]
  exact (segreChartMap m n ij).w.trans (projectivePairChartMap m n ij).w.symm

/-- The Segre morphism bundled in the category over the actual complex base. -/
def segreOverMap (m n : ℕ) :
    projectivePair m n ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (SegreCoordinates.segreDimension m n)) :=
  Over.homMk (segreMap m n) (segreMap_over m n)

@[reassoc (attr := simp)]
theorem chartMap_segreOverMap (m n : ℕ) (ij : Fin (m + 1) × Fin (n + 1)) :
    projectivePairChartMap m n ij ≫ segreOverMap m n = segreChartMap m n ij := by
  apply Over.OverMorphism.ext
  exact chartMap_segreMap m n ij

end

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory

/-- Coordinate opens pull back to the basic opens of the chosen regular
coordinate functions. -/
theorem projectiveMapOfCoordinates_preimage_coordinate {X : Scheme}
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) {n : ℕ} (v : Fin (n + 1) → Γ(X, ⊤))
    (i : Fin (n + 1)) (hv : v i = 1) (k : Fin (n + 1)) :
    ProjectiveCoordinates.projectiveMapOfCoordinates f v i hv ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n k = X.basicOpen (v k) := by
  simpa only [ProjectiveCoordinates.coordinateSectionsMap_X] using ProjectiveCoordinates.projectiveMapOfCoordinates_preimage_basicOpen
    f v i hv (MvPolynomial.X k) Nat.zero_lt_one (MvPolynomial.isHomogeneous_X ℂ k)

/-- A Segre coordinate is nonzero exactly when the corresponding coordinate
in each factor is nonzero, as an equality of actual scheme opens. -/
theorem segreMapOfCoordinates_preimage_pair {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) {m n : ℕ}
    (v : Fin (m + 1) → Γ(X, ⊤)) (w : Fin (n + 1) → Γ(X, ⊤))
    (i : Fin (m + 1)) (j : Fin (n + 1)) (hv : v i = 1) (hw : w j = 1)
    (k : Fin (m + 1)) (l : Fin (n + 1)) :
    SegreCoordinates.segreMapOfCoordinates f v w i j hv hw ⁻¹ᵁ
        Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (SegreCoordinates.segreDimension m n) (SegreCoordinates.segreIndexEquiv m n (k, l)) =
      (ProjectiveCoordinates.projectiveMapOfCoordinates f v i hv ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen m k) ⊓
        (ProjectiveCoordinates.projectiveMapOfCoordinates f w j hw ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n l) := by
  unfold SegreCoordinates.segreMapOfCoordinates
  rw [projectiveMapOfCoordinates_preimage_coordinate,
    projectiveMapOfCoordinates_preimage_coordinate, projectiveMapOfCoordinates_preimage_coordinate,
    SegreCoordinates.segreVector_pair, Scheme.basicOpen_mul]

set_option backward.isDefEq.respectTransparency false in
/-- The same coordinate-open formula holds for the glued global Segre map. -/
theorem segreMap_preimage_coordinate (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreMap m n ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (SegreCoordinates.segreDimension m n) (SegreCoordinates.segreIndexEquiv m n (i, j)) =
      ((fst (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))).left ⁻¹ᵁ
        Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen m i) ⊓
      ((snd (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))).left ⁻¹ᵁ
        Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n j) := by
  have hlocal (kl : Fin (m + 1) × Fin (n + 1)) :
      (projectivePairChartMap m n kl).left ⁻¹ᵁ
          (segreMap m n ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (SegreCoordinates.segreDimension m n) (SegreCoordinates.segreIndexEquiv m n (i, j))) =
        (projectivePairChartMap m n kl).left ⁻¹ᵁ
          (((fst (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))).left ⁻¹ᵁ
            Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen m i) ⊓
          ((snd (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))).left ⁻¹ᵁ
            Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n j)) := by
    rw [← Scheme.Hom.comp_preimage, chartMap_segreMap]
    change SegreCoordinates.segreMapOfCoordinates (projectivePairChart m n kl).hom
      (leftChartTuple (𝟙 (projectivePairChart m n kl))) (rightChartTuple (𝟙 (projectivePairChart m n kl)))
      kl.1 kl.2 (leftChartTuple_normalized _) (rightChartTuple_normalized _) ⁻¹ᵁ _ = _
    rw [segreMapOfCoordinates_preimage_pair, leftChartTuple_map, rightChartTuple_map]
    simp only [Category.id_comp, Over.comp_left, Scheme.Hom.comp_preimage, Scheme.Hom.preimage_inf]
  ext x
  obtain ⟨kl, y, hy⟩ := (ProjectiveCover.projectiveProductCover m n).exists_eq x
  change (projectivePairChartMap m n kl).left y = x at hy
  rw [← hy]
  exact congrArg (fun U : (projectivePairChart m n kl).left.Opens => y ∈ U) (hlocal kl) |>.to_iff

/-- The actual polynomial chart inclusion has the usual coordinate-open range. -/
theorem range_projectiveAffineChartMap (n : ℕ) (i : Fin (n + 1)) :
    Set.range (Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i) = Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i := by
  change Set.range ((Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι ∘ (Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec n i).inv) = _
  rw [Set.range_comp, (Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec n i).inv.surjective.range_eq,
    Set.image_univ, Scheme.Opens.range_ι]

/-- The inverse image of a Segre coordinate open is exactly the corresponding
product chart, preparing the target-local closed-immersion check. -/
theorem segreMap_preimage_coordinate_range (m n : ℕ) (ij : Fin (m + 1) × Fin (n + 1)) :
    (segreMap m n ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (SegreCoordinates.segreDimension m n) (SegreCoordinates.segreIndexEquiv m n ij) :
      Set (projectivePair m n).left) = Set.range (projectivePairChartMap m n ij).left := by
  rw [segreMap_preimage_coordinate m n ij.1 ij.2]
  change _ = Set.range (ProjectiveCover.polynomialChartOverMap m ij.1 ⊗ₘ ProjectiveCover.polynomialChartOverMap n ij.2).left
  rw [ProjectiveCover.range_tensorHom]
  change _ = (fst (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))).left ⁻¹'
      Set.range (Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap m ij.1) ∩
    (snd (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))).left ⁻¹'
      Set.range (Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n ij.2)
  rw [range_projectiveAffineChartMap, range_projectiveAffineChartMap]
  rfl

end

end OAI.AlgebraicGeometry.Albanese.Construction.SegreLocal
