import OAI.AlgebraicGeometry.Albanese.Construction.ClosedPoints
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveVectorScale
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover

/-! # Projective Coordinates -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProjectiveCoordinates.Constructions.Products

noncomputable section

section

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Albanese.Construction.ClosedPoints

/-- Scalars as global regular functions, using the actual structure morphism. -/
def scalarGlobalSections {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) : ℂ →+* Γ(X, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom

/-- Substitute a tuple of global regular functions for homogeneous variables. -/
def coordinateSectionsMap {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) {n : ℕ}
    (v : Fin (n + 1) → Γ(X, ⊤)) : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n →+* Γ(X, ⊤) :=
  MvPolynomial.eval₂Hom (scalarGlobalSections f) v

@[simp]
theorem coordinateSectionsMap_X {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) {n : ℕ}
    (v : Fin (n + 1) → Γ(X, ⊤)) (i : Fin (n + 1)) :
    coordinateSectionsMap f v (MvPolynomial.X i) = v i := by
  simp [coordinateSectionsMap]

@[simp]
theorem coordinateSectionsMap_C {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) {n : ℕ}
    (v : Fin (n + 1) → Γ(X, ⊤)) (c : ℂ) :
    coordinateSectionsMap f v (MvPolynomial.C c) = scalarGlobalSections f c := by
  simp [coordinateSectionsMap]

/-- A tuple with one coordinate equal to one generates the irrelevant ideal. -/
theorem coordinateSectionsMap_irrelevant {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) {n : ℕ}
    (v : Fin (n + 1) → Γ(X, ⊤)) (i : Fin (n + 1)) (hv : v i = 1) :
    (HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading n)).toIdeal.map
      (coordinateSectionsMap f v) = ⊤ := by
  apply Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem (coordinateSectionsMap f v)
      (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.zero_lt_one
        (MvPolynomial.isHomogeneous_X ℂ i)))
  simp [hv]

/-- A normalized tuple of regular functions defines an actual projective
scheme morphism. This will be applied on the product coordinate charts. -/
def projectiveMapOfCoordinates {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) {n : ℕ}
    (v : Fin (n + 1) → Γ(X, ⊤)) (i : Fin (n + 1)) (hv : v i = 1) : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n :=
  Proj.fromOfGlobalSections (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (coordinateSectionsMap f v)
    (coordinateSectionsMap_irrelevant f v i hv)

@[reassoc (attr := simp)]
theorem projectiveMapOfCoordinates_over {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) {n : ℕ}
    (v : Fin (n + 1) → Γ(X, ⊤)) (i : Fin (n + 1)) (hv : v i = 1) :
    projectiveMapOfCoordinates f v i hv ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n = f := by
  have hc : CommRingCat.ofHom (Foundations.Scheme.ProjectiveSpace.degreeZeroConstants n).toRingHom ≫
      CommRingCat.ofHom ((coordinateSectionsMap f v).comp
        (algebraMap (Foundations.Scheme.ProjectiveSpace.projectiveGrading n 0) (Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n))) =
      (Scheme.ΓSpecIso (.of ℂ)).inv ≫ f.appTop := by
    ext c
    exact coordinateSectionsMap_C f v c
  rw [Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase, ← Category.assoc, projectiveMapOfCoordinates,
    Proj.fromOfGlobalSections_toSpecZero, Category.assoc, ← Spec.map_comp, hc,
    Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- Pulling back a homogeneous projective open tests invertibility of the
corresponding polynomial in the chosen regular functions. -/
theorem projectiveMapOfCoordinates_preimage_basicOpen {X : Scheme}
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) {n : ℕ} (v : Fin (n + 1) → Γ(X, ⊤))
    (i : Fin (n + 1)) (hv : v i = 1)
    (p : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n) {d : ℕ} (hd : 0 < d) (hp : p ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading n d) :
    projectiveMapOfCoordinates f v i hv ⁻¹ᵁ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) p =
      X.basicOpen (coordinateSectionsMap f v p) :=
  Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ hd hp

end

section

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Albanese.Construction.ClosedPoints

/-- Evaluate a global regular function at an actual complex-valued point. -/
def pointEvaluate {X : Scheme} (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) : Γ(X, ⊤) →+* ℂ :=
  (Scheme.ΓSpecIso (.of ℂ)).hom.hom.comp p.appTop.hom

theorem pointEvaluate_scalar {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) (hp : p ≫ f = 𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) :
    (pointEvaluate p).comp (scalarGlobalSections f) = RingHom.id ℂ := by
  have h : f.appTop ≫ p.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, hp]
    rfl
  ext c
  change ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (f.appTop ≫ p.appTop) ≫
    (Scheme.ΓSpecIso (.of ℂ)).hom) c = c
  rw [h]
  simp

/-- Evaluation commutes with pullback of regular functions. -/
theorem pointEvaluate_comp {X Y : Scheme} (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) (h : X ⟶ Y) :
    pointEvaluate (p ≫ h) = (pointEvaluate p).comp h.appTop.hom := by
  simp only [pointEvaluate, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_assoc]

/-- A normalized regular-function tuple stays nonzero after evaluation. -/
theorem pointEvaluate_tuple_ne_zero {X : Scheme} (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) {n : ℕ}
    (v : Fin (n + 1) → Γ(X, ⊤)) (i : Fin (n + 1)) (hv : v i = 1) :
    (fun j => pointEvaluate p (v j)) ≠ 0 := by
  intro h
  have hc := congrFun h i
  simp [hv] at hc

/-- Evaluation of coordinate polynomials commutes with ordinary polynomial
substitution into the evaluated tuple. -/
theorem pointEvaluate_coordinateSections {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) (hp : p ≫ f = 𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) {n : ℕ}
    (v : Fin (n + 1) → Γ(X, ⊤)) :
    (pointEvaluate p).comp (coordinateSectionsMap f v) =
      MvPolynomial.eval (fun j => pointEvaluate p (v j)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simpa using DFunLike.congr_fun (pointEvaluate_scalar f p hp) c
  · intro j
    simp

set_option backward.isDefEq.respectTransparency false in
/-- Membership in a regular-function basic open at a complex point is tested
by the corresponding complex value. -/
theorem pointEvaluate_mem_basicOpen {X : Scheme} (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) (r : Γ(X, ⊤)) :
    p (IsLocalRing.closedPoint ℂ) ∈ X.basicOpen r ↔ pointEvaluate p r ≠ 0 := by
  change IsLocalRing.closedPoint ℂ ∈ p ⁻¹ᵁ X.basicOpen r ↔ _
  rw [Scheme.preimage_basicOpen]
  have hr : p.appTop r = (Scheme.ΓSpecIso (.of ℂ)).inv (pointEvaluate p r) := by
    simp [pointEvaluate]
  change IsLocalRing.closedPoint ℂ ∈ Foundations.Scheme.ProjectiveSpace.complexBase.basicOpen (p.appTop r) ↔ _
  rw [hr, basicOpen_eq_of_affine (R := .of ℂ)]
  rw [Subsingleton.elim (IsLocalRing.closedPoint ℂ) (default : Foundations.Scheme.ProjectiveSpace.complexBase)]
  change (pointEvaluate p r ∉ (default : Foundations.Scheme.ProjectiveSpace.complexBase).asIdeal) ↔ _
  rw [Scheme.default_asIdeal]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The coordinate morphism at a complex point has precisely the evaluated
homogeneous coordinates. -/
theorem projectiveMapOfCoordinates_point {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) (hp : p ≫ f = 𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) {n : ℕ}
    (v : Fin (n + 1) → Γ(X, ⊤)) (i : Fin (n + 1)) (hv : v i = 1)
    (hw : (fun j => pointEvaluate p (v j)) ≠ 0) :
    p ≫ projectiveMapOfCoordinates f v i hv =
      Foundations.Scheme.ProjectiveVectorPoint.projectiveVectorPoint (fun j => pointEvaluate p (v j)) hw := by
  apply ext_of_apply_closedPoint_eq (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
    (by rw [Category.assoc, projectiveMapOfCoordinates_over, hp])
    (Foundations.Scheme.ProjectiveVectorPoint.projectiveVectorPoint_over_base _ hw)
  have : ((p ≫ projectiveMapOfCoordinates f v i hv) (IsLocalRing.closedPoint ℂ)).asHomogeneousIdeal.toIdeal.IsPrime :=
    ((p ≫ projectiveMapOfCoordinates f v i hv) (IsLocalRing.closedPoint ℂ)).isPrime
  have : (Foundations.Scheme.ProjectiveVectorPoint.projectiveVectorPoint (fun j => pointEvaluate p (v j)) hw
      (IsLocalRing.closedPoint ℂ)).asHomogeneousIdeal.toIdeal.IsPrime :=
    (Foundations.Scheme.ProjectiveVectorPoint.projectiveVectorPoint (fun j => pointEvaluate p (v j)) hw (IsLocalRing.closedPoint ℂ)).isPrime
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro d q hq
  cases d with
  | zero =>
    obtain ⟨c, rfl⟩ : ∃ c : ℂ, q = MvPolynomial.C c :=
      ⟨_, Foundations.Scheme.HomogeneousEvalMap.eq_C_of_isHomogeneous_zero hq⟩
    by_cases hc : c = 0
    · simp [hc]
    · have hu : IsUnit (MvPolynomial.C c : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n) :=
        (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
      constructor <;> intro h
      · exact False.elim (Ideal.notMem_of_isUnit _ hu h)
      · exact False.elim (Ideal.notMem_of_isUnit _ hu h)
  | succ d =>
    apply not_iff_not.mp
    change projectiveMapOfCoordinates f v i hv (p (IsLocalRing.closedPoint ℂ)) ∈
      Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) q ↔
      Foundations.Scheme.ProjectiveVectorPoint.projectiveVectorPoint (fun j => pointEvaluate p (v j)) hw (IsLocalRing.closedPoint ℂ) ∈
        Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) q
    rw [Foundations.Scheme.ProjectiveVectorPoint.projectiveVectorPoint_mem_basicOpen_iff _ hw q (Nat.succ_pos d) hq]
    change p (IsLocalRing.closedPoint ℂ) ∈
      projectiveMapOfCoordinates f v i hv ⁻¹ᵁ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) q ↔ _
    rw [projectiveMapOfCoordinates_preimage_basicOpen f v i hv q (Nat.succ_pos d) hq,
      pointEvaluate_mem_basicOpen]
    exact iff_of_eq (congrArg (fun z : ℂ => z ≠ 0)
      (DFunLike.congr_fun (pointEvaluate_coordinateSections f p hp v) q))

/-- Normalized coordinate maps agree if their evaluated tuples differ by a
nonzero scalar at every complex point. This provides the overlap test for
gluing the local Segre maps. -/
theorem projectiveMapOfCoordinates_eq_of_point_scalars (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [LocallyOfFiniteType X.hom] [IsReduced X.left] {n : ℕ}
    (v w : Fin (n + 1) → Γ(X.left, ⊤)) (i j : Fin (n + 1))
    (hv : v i = 1) (hw : w j = 1)
    (hscale : ∀ p : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X, ∃ c : ℂ, c ≠ 0 ∧
      (fun k => pointEvaluate p.left (w k)) = c • (fun k => pointEvaluate p.left (v k))) :
    projectiveMapOfCoordinates X.hom v i hv = projectiveMapOfCoordinates X.hom w j hw := by
  let P := Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  have : LocallyOfFiniteType P.hom := by dsimp [P]; infer_instance
  have : IsSeparated P.hom := by dsimp [P]; infer_instance
  let a : X ⟶ P := Over.homMk _ (projectiveMapOfCoordinates_over X.hom v i hv)
  let b : X ⟶ P := Over.homMk _ (projectiveMapOfCoordinates_over X.hom w j hw)
  have heq : a = b := by
    apply Albanese.Construction.ClosedPoints.hom_ext_of_points X P a b
    intro p
    apply Over.OverMorphism.ext
    change p.left ≫ projectiveMapOfCoordinates X.hom v i hv =
      p.left ≫ projectiveMapOfCoordinates X.hom w j hw
    rw [projectiveMapOfCoordinates_point X.hom p.left p.w v i hv
      (pointEvaluate_tuple_ne_zero p.left v i hv),
      projectiveMapOfCoordinates_point X.hom p.left p.w w j hw
        (pointEvaluate_tuple_ne_zero p.left w j hw)]
    obtain ⟨c, hc, hcw⟩ := hscale p
    have hn : c • (fun k => pointEvaluate p.left (v k)) ≠ 0 := by
      rw [← hcw]
      exact pointEvaluate_tuple_ne_zero p.left w j hw
    simpa only [hcw] using
      (Foundations.Scheme.ProjectiveVectorScale.projectiveVectorPoint_smul _ (pointEvaluate_tuple_ne_zero p.left v i hv) c hc hn).symm
  exact congrArg Over.Hom.left heq

end

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Albanese.Construction.ClosedPoints

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back a normalized coordinate tuple pulls back its actual
projective scheme morphism. -/
theorem projectiveMapOfCoordinates_comp (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [LocallyOfFiniteType X.hom] [IsReduced X.left]
    (h : X ⟶ Y) {n : ℕ} (v : Fin (n + 1) → Γ(Y.left, ⊤))
    (i : Fin (n + 1)) (hv : v i = 1) :
    h.left ≫ projectiveMapOfCoordinates Y.hom v i hv =
      projectiveMapOfCoordinates X.hom (fun k => h.left.appTop (v k)) i (by simp [hv]) := by
  let P := Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  have : LocallyOfFiniteType P.hom := by dsimp [P]; infer_instance
  have : IsSeparated P.hom := by dsimp [P]; infer_instance
  let a : X ⟶ P := h ≫ Over.homMk _ (projectiveMapOfCoordinates_over Y.hom v i hv)
  let b : X ⟶ P := Over.homMk _
    (projectiveMapOfCoordinates_over X.hom (fun k => h.left.appTop (v k)) i (by simp [hv]))
  have heq : a = b := by
    apply Albanese.Construction.ClosedPoints.hom_ext_of_points X P a b
    intro p
    apply Over.OverMorphism.ext
    change p.left ≫ h.left ≫ projectiveMapOfCoordinates Y.hom v i hv =
      p.left ≫ projectiveMapOfCoordinates X.hom (fun k => h.left.appTop (v k)) i (by simp [hv])
    rw [← Category.assoc]
    have hp : (p.left ≫ h.left) ≫ Y.hom = 𝟙 Foundations.Scheme.ProjectiveSpace.complexBase := by
      rw [Category.assoc, h.w]
      exact p.w
    rw [projectiveMapOfCoordinates_point Y.hom (p.left ≫ h.left) hp v i hv
      (pointEvaluate_tuple_ne_zero (p.left ≫ h.left) v i hv),
      projectiveMapOfCoordinates_point X.hom p.left p.w (fun k => h.left.appTop (v k)) i
        (by simp [hv]) (pointEvaluate_tuple_ne_zero p.left _ i (by simp [hv]))]
    congr 1
  exact congrArg Over.Hom.left heq

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProjectiveCoordinates.Constructions.Products
