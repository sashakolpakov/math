import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.TotalBoundaries
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses
import OAI.NumberTheory.PadicHodge.IntegralComparison.BilinearQuotient

/-! # Cohomology Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.CohomologyCup.Cech

noncomputable section

/-! The product induced on the original categorical homology of the
Čech–de Rham total complex. Both boundary relations are proved before
descending the bilinear map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses

universe u

variable (R : Type u) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R)))
  (N : SimplicialObject (FormalCoproduct.{u} X.left.Opens))

local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.TotalCup.Cech.total R X N

def cycleCup (p q : ℕ) : Module.CochainClasses.cycles K p →ₗ[R] Module.CochainClasses.cycles K q →ₗ[R] Module.CochainClasses.cycles K (p + q) where
  toFun x :=
    { toFun := fun y => ⟨TotalCup.Cech.totalCup R X N p q x.val y.val,
        TotalBoundaries.CechCup.totalCup_closed R X N p q x.val y.val x.property y.property⟩
      map_add' := fun y z => Subtype.ext ((TotalCup.Cech.totalCup R X N p q x.val).map_add y.val z.val)
      map_smul' := fun r y => Subtype.ext ((TotalCup.Cech.totalCup R X N p q x.val).map_smul r y.val) }
  map_add' x x' := by
    apply LinearMap.ext
    intro y
    exact Subtype.ext (DFunLike.congr_fun ((TotalCup.Cech.totalCup R X N p q).map_add x.val x'.val) y.val)
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    exact Subtype.ext (DFunLike.congr_fun ((TotalCup.Cech.totalCup R X N p q).map_smul r x.val) y.val)

def cycleCupClass (p q : ℕ) : Module.CochainClasses.cycles K p →ₗ[R] Module.CochainClasses.cycles K q →ₗ[R] (K).homology (p + q) :=
  (cycleCup R X N p q).compr₂ (Module.CochainClasses.classMap K (p + q))

theorem cycleCupClass_boundary_left (p q : ℕ) (x : Module.CochainClasses.cycles K p) (y : Module.CochainClasses.cycles K q)
    (hx : x ∈ Module.CochainClasses.boundaries K p) : cycleCupClass R X N p q x y = 0 := by
  obtain ⟨b, hb⟩ := hx
  have hx0 : Module.CochainClasses.classMap K p x = 0 :=
    (Module.CochainClasses.classMap_eq_zero_iff K p x).mpr ⟨b, congrArg Subtype.val hb⟩
  cases p with
  | zero =>
      have hxz := (Module.CochainClasses.classMap_zero_eq_zero_iff K x).mp hx0
      rw [hxz, map_zero]
      rfl
  | succ p =>
      obtain ⟨z, hz⟩ := (Module.CochainClasses.classMap_succ_eq_zero_iff K p x).mp hx0
      apply (Module.CochainClasses.classMap_eq_zero_iff K ((p + 1) + q) (cycleCup R X N (p + 1) q x y)).mpr
      have hp : (ComplexShape.up ℕ).prev ((p + 1) + q) = p + q :=
        (ComplexShape.up ℕ).prev_eq' (by change p + q + 1 = (p + 1) + q; omega)
      rw [hp]
      refine ⟨TotalCup.Cech.totalCup R X N p q z y.val, ?_⟩
      exact (TotalBoundaries.CechCup.differential_totalCup_right_closed R X N p q ((p + 1) + q) rfl z y.val y.property).trans
        (congrArg (fun w => TotalCup.Cech.totalCup R X N (p + 1) q w y.val) hz)

theorem cycleCupClass_boundary_right (p q : ℕ) (x : Module.CochainClasses.cycles K p) (y : Module.CochainClasses.cycles K q)
    (hy : y ∈ Module.CochainClasses.boundaries K q) : cycleCupClass R X N p q x y = 0 := by
  obtain ⟨b, hb⟩ := hy
  have hy0 : Module.CochainClasses.classMap K q y = 0 :=
    (Module.CochainClasses.classMap_eq_zero_iff K q y).mpr ⟨b, congrArg Subtype.val hb⟩
  cases q with
  | zero =>
      have hyz := (Module.CochainClasses.classMap_zero_eq_zero_iff K y).mp hy0
      rw [hyz, map_zero]
  | succ q =>
      obtain ⟨z, hz⟩ := (Module.CochainClasses.classMap_succ_eq_zero_iff K q y).mp hy0
      apply (Module.CochainClasses.classMap_eq_zero_iff K (p + (q + 1)) (cycleCup R X N p (q + 1) x y)).mpr
      have hp : (ComplexShape.up ℕ).prev (p + (q + 1)) = p + q :=
        (ComplexShape.up ℕ).prev_eq' (by change p + q + 1 = p + (q + 1); omega)
      rw [hp]
      refine ⟨(-1 : ℤ) ^ p • TotalCup.Cech.totalCup R X N p q x.val z, ?_⟩
      exact (TotalBoundaries.CechCup.differential_totalCup_left_closed R X N p q (p + (q + 1)) rfl x.val z x.property).trans
        (congrArg (fun w => TotalCup.Cech.totalCup R X N p (q + 1) x.val w) hz)

def cohomologyCup (p q : ℕ) : (K).homology p →ₗ[R] (K).homology q →ₗ[R] (K).homology (p + q) :=
  ((BilinearQuotient.lift₂ (Module.CochainClasses.boundaries K p) (Module.CochainClasses.boundaries K q) (cycleCupClass R X N p q)
    (fun x hx y => cycleCupClass_boundary_left R X N p q x y hx)
    (fun x y hy => cycleCupClass_boundary_right R X N p q x y hy)).comp
      (Module.CochainClasses.quotientIso K p).hom.hom).compl₂ (Module.CochainClasses.quotientIso K q).hom.hom

omit [Algebra ℚ R] in
theorem quotient_classMap (p : ℕ) (x : Module.CochainClasses.cycles K p) :
    (Module.CochainClasses.quotientIso K p).hom (Module.CochainClasses.classMap K p x) = (Module.CochainClasses.boundaries K p).mkQ x :=
  ConcreteCategory.congr_hom (Module.CochainClasses.quotientIso K p).inv_hom_id ((Module.CochainClasses.boundaries K p).mkQ x)

theorem cup_class (p q : ℕ) (x : Module.CochainClasses.cycles K p) (y : Module.CochainClasses.cycles K q) :
    cohomologyCup R X N p q (Module.CochainClasses.classMap K p x) (Module.CochainClasses.classMap K q y) =
      Module.CochainClasses.classMap K (p + q) (cycleCup R X N p q x y) := by
  change BilinearQuotient.lift₂ (Module.CochainClasses.boundaries K p) (Module.CochainClasses.boundaries K q)
    (cycleCupClass R X N p q)
    (fun x hx y => cycleCupClass_boundary_left R X N p q x y hx)
    (fun x y hy => cycleCupClass_boundary_right R X N p q x y hy)
    ((Module.CochainClasses.quotientIso K p).hom (Module.CochainClasses.classMap K p x)) ((Module.CochainClasses.quotientIso K q).hom (Module.CochainClasses.classMap K q y)) = _
  rw [quotient_classMap, quotient_classMap, BilinearQuotient.lift₂_mkQ]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.CohomologyCup.Cech
