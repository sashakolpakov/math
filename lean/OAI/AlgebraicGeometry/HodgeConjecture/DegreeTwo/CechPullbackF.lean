import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Obj

/-! # Cech Pullback F -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CechPullbackF.Constructions.CechPullback

noncomputable section

section

/-!
# DegreeTwo: pullback of the rational Cech complex across actual continuous maps

These are the actual pulled-back cover and locally constant cochain maps.
The construction is needed to restrict the logarithmic Chern class to the
complement of the divisor of a rational section.
-/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Obj.RationalCech

variable {X Y : TopCat.{0}} {I : Type} (f : Y ⟶ X) (U : I → Opens X)

/-- The literal inverse-image open cover. -/
def pulledCover (i : I) : Opens Y := ⟨f ⁻¹' U i, (U i).isOpen.preimage f.hom.continuous⟩

/-- The original continuous map restricted to every finite cover intersection. -/
def intersectionMap {n : ℕ} (a : Fin (n + 1) → I) :
    TopCat.of (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (pulledCover f U) a) ⟶ TopCat.of (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) :=
  TopCat.ofHom ⟨fun x => ⟨f x.val, (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection U a _).mpr
      (fun k => (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (pulledCover f U) a k x.property))⟩,
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- A covering family remains a covering family after actual pullback. -/
theorem pulledCover_covers (hU : ∀ x : X, ∃ i, x ∈ U i) :
    ∀ y : Y, ∃ i, y ∈ pulledCover f U i := fun y => hU (f y)

/-- Pull locally constant rational functions back on every cover intersection. -/
def locallyConstantMap (n : ℕ) :
    DivisorClass.Chern.Rational.Cech.RationalCech.CechCochain (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantPresheaf X) U n →ₗ[ℚ]
      DivisorClass.Chern.Rational.Cech.RationalCech.CechCochain (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantPresheaf Y) (pulledCover f U) n where
  toFun c a := ⟨fun y => c a (intersectionMap f U a y),
    (c a).isLocallyConstant.comp_continuous (intersectionMap f U a).hom.continuous⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Forgetting or repeating indices commutes with the actual continuous pullback. -/
theorem locallyConstantMap_precomp {n m : ℕ} (θ : Fin (n + 1) → Fin (m + 1))
    (c : DivisorClass.Chern.Rational.Cech.RationalCech.CechCochain (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantPresheaf X) U n) :
    locallyConstantMap f U m (DivisorClass.Chern.Rational.Cech.RationalCech.cechPrecomp (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantPresheaf X) U θ c) =
      DivisorClass.Chern.Rational.Cech.RationalCech.cechPrecomp (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantPresheaf Y) (pulledCover f U) θ
        (locallyConstantMap f U n c) := by
  funext a
  apply LocallyConstant.ext
  intro y
  rfl

/-- The actual rational cosimplicial map induced by pullback of functions. -/
def locallyConstantNat :
    DivisorClass.Chern.Rational.Cech.RationalCech.cechCosimplicial (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantPresheaf X) U ⟶
      DivisorClass.Chern.Rational.Cech.RationalCech.cechCosimplicial (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantPresheaf Y) (pulledCover f U) where
  app n := ModuleCat.ofHom (locallyConstantMap f U n.len)
  naturality n m θ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact locallyConstantMap_precomp f U θ.toOrderHom c

/-- Pullback on the genuine locally constant rational Cech complexes. -/
def locallyConstantCochainMap :
    DivisorClass.Chern.Rational.Cech.RationalCech.cechComplex (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantPresheaf X) U ⟶
      DivisorClass.Chern.Rational.Cech.RationalCech.cechComplex (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantPresheaf Y) (pulledCover f U) :=
  AlgebraicTopology.AlternatingCofaceMapComplex.map (locallyConstantNat f U)

@[simp]
theorem locallyConstantCochainMap_f (n : ℕ) :
    (locallyConstantCochainMap f U).f n = ModuleCat.ofHom (locallyConstantMap f U n) := rfl

/-- Consequently the signed differential commutes with pullback on every cochain. -/
theorem locallyConstantMap_delta (n : ℕ)
    (c : DivisorClass.Chern.Rational.Cech.RationalCech.CechCochain (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantPresheaf X) U n) :
    locallyConstantMap f U (n + 1) (DivisorClass.Chern.Rational.Cech.RationalCech.cechDelta (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantPresheaf X) U n c) =
      DivisorClass.Chern.Rational.Cech.RationalCech.cechDelta (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantPresheaf Y) (pulledCover f U) n
        (locallyConstantMap f U n c) := by
  have h := (locallyConstantCochainMap f U).comm n (n + 1)
  rw [DivisorClass.Chern.Rational.Cech.RationalCech.cechComplex_d, DivisorClass.Chern.Rational.Cech.RationalCech.cechComplex_d, locallyConstantCochainMap_f, locallyConstantCochainMap_f] at h
  exact (ConcreteCategory.congr_hom h c).symm

end

section

/-! Actual continuous pullback on the rational singular Cech double complex. -/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Obj.RationalCech

variable {X Y : TopCat.{0}} {I : Type} (f : Y ⟶ X) (U : I → Opens X) (M : ModuleCat.{0} ℚ)

/-- Actual singular pullback on each intersection, in the two explicit degrees. -/
def singularMap (p q : ℕ) :
    DivisorClass.Chern.Rational.Cech.RationalCech.CechCochain (OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X q) U p →ₗ[ℚ]
      DivisorClass.Chern.Rational.Cech.RationalCech.CechCochain (OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M Y q) (pulledCover f U) p where
  toFun c a := (OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (intersectionMap f U a)).f q (c a)
  map_add' c d := by funext a; exact map_add _ _ _
  map_smul' r c := by funext a; exact map_smul _ _ _

/-- Pullback commutes with forgetting or repeating cover indices. -/
theorem singularMap_precomp {n m : ℕ} (θ : Fin (n + 1) → Fin (m + 1)) (q : ℕ)
    (c : DivisorClass.Chern.Rational.Cech.RationalCech.CechCochain (OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X q) U n) :
    singularMap f U M m q (DivisorClass.Chern.Rational.Cech.RationalCech.cechPrecomp (OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X q) U θ c) =
      DivisorClass.Chern.Rational.Cech.RationalCech.cechPrecomp (OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M Y q) (pulledCover f U) θ
        (singularMap f U M n q c) := by
  funext a
  change ((OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M ((Opens.toTopCat X).map
      (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a θ))) ≫
        OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (intersectionMap f U a)).f q) (c (a ∘ θ)) =
    ((OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (intersectionMap f U (a ∘ θ)) ≫
      OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M ((Opens.toTopCat Y).map
        (homOfLE (OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp (pulledCover f U) a θ)))).f q) (c (a ∘ θ))
  erw [← OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp, ← OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp]
  rfl

/-- The horizontal cosimplicial pullback in each singular degree. -/
def singularHorizontalNat (q : ℕ) :
    DivisorClass.Chern.Rational.Cech.RationalCech.cechCosimplicial (OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X q) U ⟶
      DivisorClass.Chern.Rational.Cech.RationalCech.cechCosimplicial (OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M Y q) (pulledCover f U) where
  app n := ModuleCat.ofHom (singularMap f U M n.len q)
  naturality n m θ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact singularMap_precomp f U M θ.toOrderHom q c

def singularHorizontalMap (q : ℕ) :
    DivisorClass.Chern.Rational.Cech.RationalCech.cechComplex (OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X q) U ⟶
      DivisorClass.Chern.Rational.Cech.RationalCech.cechComplex (OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M Y q) (pulledCover f U) :=
  AlgebraicTopology.AlternatingCofaceMapComplex.map (singularHorizontalNat f U M q)

theorem singularMap_delta (p q : ℕ)
    (c : DivisorClass.Chern.Rational.Cech.RationalCech.CechCochain (OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X q) U p) :
    singularMap f U M (p + 1) q (DivisorClass.Chern.Rational.Cech.RationalCech.cechDelta (OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X q) U p c) =
      DivisorClass.Chern.Rational.Cech.RationalCech.cechDelta (OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M Y q) (pulledCover f U) p
        (singularMap f U M p q c) := by
  have h := (singularHorizontalMap f U M q).comm p (p + 1)
  rw [DivisorClass.Chern.Rational.Cech.RationalCech.cechComplex_d, DivisorClass.Chern.Rational.Cech.RationalCech.cechComplex_d] at h
  exact (ConcreteCategory.congr_hom h c).symm

/-- Pullback commutes with the actual singular coboundary on each intersection. -/
theorem singularMap_vertical (p q : ℕ)
    (c : DivisorClass.Chern.Rational.Cech.RationalCech.CechCochain (OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X q) U p) :
    singularMap f U M p (q + 1)
      (DivisorClass.Chern.Rational.Cech.RationalCech.cechCoefficientMap U ((OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X).d q (q + 1)) p c) =
    DivisorClass.Chern.Rational.Cech.RationalCech.cechCoefficientMap (pulledCover f U) ((OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M Y).d q (q + 1)) p
      (singularMap f U M p q c) := by
  funext a
  exact (ConcreteCategory.congr_hom ((OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (intersectionMap f U a)).comm q (q + 1))
    (c a)).symm

/-- Actual pullback on a column of the singular Cech bicomplex. -/
def singularColumnMap (p : ℕ) :
    (DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechDoubleComplex X U M).X p ⟶
      (DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechDoubleComplex Y (pulledCover f U) M).X p :=
  CochainComplex.ofHom
    (fun q => ModuleCat.ofHom (singularMap f U M p q))
    (fun q => by
      rw [DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechDoubleComplex_X_d, DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechDoubleComplex_X_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact (singularMap_vertical f U M p q c).symm)

/-- Continuous pullback respects both actual Cech and singular differentials. -/
def singularDoubleComplexMap :
    DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechDoubleComplex X U M ⟶ DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechDoubleComplex Y (pulledCover f U) M :=
  CochainComplex.ofHom (singularColumnMap f U M)
    (fun p => by
      apply HomologicalComplex.Hom.ext
      funext q
      change (singularColumnMap f U M p).f q ≫
          ((DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechDoubleComplex Y (pulledCover f U) M).d p (p + 1)).f q =
        ((DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechDoubleComplex X U M).d p (p + 1)).f q ≫
          (singularColumnMap f U M (p + 1)).f q
      rw [DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechDoubleComplex_d_f, DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechDoubleComplex_d_f]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact (singularMap_delta f U M p q c).symm)

/-- The total pullback is induced by the actual map of double complexes. -/
def singularTotalMap : DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechTotal X U M ⟶ DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechTotal Y (pulledCover f U) M :=
  HomologicalComplex₂.total.map (singularDoubleComplexMap f U M) (ComplexShape.up ℕ)

/-- Each summand of the total map is the original intersectionwise pullback. -/
theorem totalInclusion_map (p q n : ℕ) (h : p + q = n) :
    DivisorClass.Chern.Rational.Cech.RationalCech.cechTotalInclusion U (OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X) p q n h ≫ (singularTotalMap f U M).f n =
      ModuleCat.ofHom (singularMap f U M p q) ≫
        DivisorClass.Chern.Rational.Cech.RationalCech.cechTotalInclusion (pulledCover f U) (OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M Y) p q n h :=
  HomologicalComplex₂.ιTotal_map (K := DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechDoubleComplex X U M)
    (L := DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechDoubleComplex Y (pulledCover f U) M)
    (φ := singularDoubleComplexMap f U M) (c₁₂ := ComplexShape.up ℕ) p q n h

end

/-!
# DegreeTwo: naturality of the actual rational Cech-to-singular comparison

Both augmentations commute with genuine continuous pullback. Inverting the
proved global singular augmentation therefore preserves that pullback, so
restriction of a logarithmic Cech class is restriction of its singular class.
-/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.Obj.RationalCech

variable {X Y : TopCat.{0}} {I : Type} (f : Y ⟶ X) (U : I → Opens X)

/-- Global singular cochains restrict compatibly to all pulled-back intersections. -/
theorem globalColumn_naturality (M : ModuleCat.{0} ℚ) (n : ℕ) :
    (DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U M).f n ≫ ModuleCat.ofHom (singularMap f U M 0 n) =
      (OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M f).f n ≫
        (DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation Y (pulledCover f U) M).f n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  funext a
  change (OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (intersectionMap f U a)).f n
      (((DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U M).f n c) a) =
    ((DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation Y (pulledCover f U) M).f n
      ((OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M f).f n c)) a
  rw [DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation_apply, DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation_apply]
  change ((OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) ≫
      OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (intersectionMap f U a)).f n) c =
    ((OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M f ≫
      OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)).f n) c
  erw [← OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp, ← OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp]
  rfl

/-- The global singular augmentation commutes with actual continuous pullback. -/
theorem globalTotal_naturality (M : ModuleCat.{0} ℚ) :
    DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechAugmentation X U M ≫ singularTotalMap f U M =
      OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M f ≫ DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechAugmentation Y (pulledCover f U) M := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechAugmentation_f, DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechAugmentation_f]
  change ((DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U M).f n ≫
      DivisorClass.Chern.Rational.Cech.RationalCech.cechTotalInclusion U (OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X) 0 n n (Nat.zero_add n)) ≫ _ =
    (OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M f).f n ≫
      ((DivisorClass.Chern.Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation Y (pulledCover f U) M).f n ≫
        DivisorClass.Chern.Rational.Cech.RationalCech.cechTotalInclusion (pulledCover f U) (OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M Y) 0 n n (Nat.zero_add n))
  have htotal := totalInclusion_map f U M 0 n n (Nat.zero_add n)
  have hcolumn := globalColumn_naturality f U M n
  erw [Category.assoc]
  erw [htotal]
  erw [← Category.assoc]
  erw [hcolumn]
  exact Category.assoc _ _ _

/-- Evaluating a pulled-back locally constant function is actual singular pullback. -/
theorem locallyConstantEvaluation_naturality (n : ℕ) :
    ModuleCat.ofHom (locallyConstantMap f U n) ≫
      ModuleCat.ofHom (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechEvaluation Y (pulledCover f U) n) =
    ModuleCat.ofHom (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechEvaluation X U n) ≫
      ModuleCat.ofHom (singularMap f U (ModuleCat.of ℚ ℚ) n 0) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  funext a
  exact ConcreteCategory.congr_hom
    (OAI.AlgebraicTopology.Cohomology.Singular.Augmentation.locallyConstantToSingularZero_naturality (ModuleCat.of ℚ ℚ) (intersectionMap f U a)) (c a)

/-- The locally constant-to-total augmentation respects actual pullback. -/
theorem locallyConstantTotal_naturality :
    locallyConstantCochainMap f U ≫ DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechToTotal Y (pulledCover f U) =
      DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechToTotal X U ≫ singularTotalMap f U (ModuleCat.of ℚ ℚ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change ModuleCat.ofHom (locallyConstantMap f U n) ≫
      (ModuleCat.ofHom (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechEvaluation Y (pulledCover f U) n) ≫
        DivisorClass.Chern.Rational.Cech.RationalCech.cechTotalInclusion (pulledCover f U) (OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) Y) n 0 n _) =
    (ModuleCat.ofHom (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechEvaluation X U n) ≫
      DivisorClass.Chern.Rational.Cech.RationalCech.cechTotalInclusion U (OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X) n 0 n _) ≫ _
  erw [Category.assoc, totalInclusion_map, ← Category.assoc, ← Category.assoc,
    locallyConstantEvaluation_naturality]

/-- Inverse of the global comparison is natural because the original augmentation is. -/
theorem singularCechIso_inv_naturality
    (hU : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    HomologicalComplex.homologyMap (singularTotalMap f U (ModuleCat.of ℚ ℚ)) n ≫
      (DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechCohomologyIso Y (pulledCover f U) (pulledCover_covers f U hU) n).inv =
    (DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechCohomologyIso X U hU n).inv ≫
      OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f n := by
  apply (cancel_epi (DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechCohomologyIso X U hU n).hom).mp
  rw [← Category.assoc, DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechCohomologyIso_hom,
    ← HomologicalComplex.homologyMap_comp, globalTotal_naturality,
    HomologicalComplex.homologyMap_comp, Category.assoc]
  rw [← DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechCohomologyIso_hom Y (pulledCover f U) (pulledCover_covers f U hU) n,
    Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, ← DivisorClass.Chern.Rational.CechComparison.RationalCech.singularCechCohomologyIso_hom X U hU n, Iso.hom_inv_id, Category.id_comp]
  rfl

/-- The canonical rational Cech-to-singular map commutes with continuous pullback. -/
theorem cechToSingular_naturality (hU : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    HomologicalComplex.homologyMap (locallyConstantCochainMap f U) n ≫
      DivisorClass.Chern.Cech.Obj.RationalCech.cechCohomologyToSingular Y (pulledCover f U) (pulledCover_covers f U hU) n =
    DivisorClass.Chern.Cech.Obj.RationalCech.cechCohomologyToSingular X U hU n ≫
      OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f n := by
  unfold DivisorClass.Chern.Cech.Obj.RationalCech.cechCohomologyToSingular
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    locallyConstantTotal_naturality, HomologicalComplex.homologyMap_comp,
    Category.assoc, singularCechIso_inv_naturality]
  exact (Category.assoc _ _ _).symm

/-- Pulling back a rational Cech cocycle gives the actual singular pullback of its class. -/
theorem classOfCechCocycle_naturality (hU : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ)
    (c : OAI.AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (DivisorClass.Chern.Rational.Cech.RationalCech.cechComplex (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantPresheaf X) U) n) :
    DivisorClass.Chern.Cech.Obj.RationalCech.singularClassOfCechCocycle Y (pulledCover f U) (pulledCover_covers f U hU) n
      (OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (locallyConstantCochainMap f U) n c) =
    OAI.AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f n (DivisorClass.Chern.Cech.Obj.RationalCech.singularClassOfCechCocycle X U hU n c) := by
  unfold DivisorClass.Chern.Cech.Obj.RationalCech.singularClassOfCechCocycle
  rw [← OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  exact ConcreteCategory.congr_hom (cechToSingular_naturality f U hU n)
    (OAI.AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (DivisorClass.Chern.Rational.Cech.RationalCech.cechComplex (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantPresheaf X) U) n c)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CechPullbackF.Constructions.CechPullback
