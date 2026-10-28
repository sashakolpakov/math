import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.HomNaturality
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.Linear
import Mathlib.CategoryTheory.Linear.Yoneda

/-! # Cohomology Maps -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps

noncomputable section

/-! Contravariant maps on the actual cohomology of projective resolutions,
with composition and addition independent of all choices of lifts. -/

open _root_.CategoryTheory Opposite

set_option backward.isDefEq.respectTransparency false

universe u v w z
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type w} [Category.{z} D] [Abelian D]
  (F : Cᵒᵖ ⥤ D) [F.Additive]

instance : (IntegralComparison.ProjectiveResolution.HomNaturality.functor F).Additive := by
  dsimp [IntegralComparison.ProjectiveResolution.HomNaturality.functor]
  infer_instance

abbrev cohomology {M : C} (P : ProjectiveResolution M) (n : ℕ) :=
  ((IntegralComparison.ProjectiveResolution.HomNaturality.functor F).obj (op P.complex)).homology n

def map {M N : C} (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (f : M ⟶ N) (n : ℕ) : cohomology F Q n ⟶ cohomology F P n :=
  IntegralComparison.ProjectiveResolution.HomNaturality.map F (ProjectiveResolution.lift f P Q) n

theorem map_eq {M N : C} (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (f : M ⟶ N) (a : P.complex ⟶ Q.complex)
    (ha : a ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) (n : ℕ) :
    CohomologyMaps.map F P Q f n = IntegralComparison.ProjectiveResolution.HomNaturality.map F a n :=
  IntegralComparison.ProjectiveResolution.HomNaturality.map_eq_of_homotopy F
    (ProjectiveResolution.liftHomotopy f _ a (ProjectiveResolution.lift_commutes f P Q) ha) n

@[simp] theorem map_id {M : C} (P : ProjectiveResolution M) (n : ℕ) :
    CohomologyMaps.map F P P (𝟙 M) n = 𝟙 (cohomology F P n) := by
  rw [CohomologyMaps.map, IntegralComparison.ProjectiveResolution.HomNaturality.map_eq_of_homotopy F
    (ProjectiveResolution.liftIdHomotopy M P) n]
  simp [IntegralComparison.ProjectiveResolution.HomNaturality.map]

theorem map_comp {M N T : C} (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (V : ProjectiveResolution T) (f : M ⟶ N) (g : N ⟶ T) (n : ℕ) :
    CohomologyMaps.map F P V (f ≫ g) n = CohomologyMaps.map F Q V g n ≫ CohomologyMaps.map F P Q f n := by
  rw [CohomologyMaps.map, IntegralComparison.ProjectiveResolution.HomNaturality.map_eq_of_homotopy F
    (ProjectiveResolution.liftCompHomotopy f g P Q V) n]
  exact IntegralComparison.ProjectiveResolution.HomNaturality.map_comp F _ _ n

@[simp] theorem map_zero {M N : C} (P : ProjectiveResolution M)
    (Q : ProjectiveResolution N) (n : ℕ) : CohomologyMaps.map F P Q 0 n = 0 := by
  rw [map_eq F P Q 0 0 (by simp) n]
  simp [IntegralComparison.ProjectiveResolution.HomNaturality.map]

theorem map_add {M N : C} (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (f g : M ⟶ N) (n : ℕ) : CohomologyMaps.map F P Q (f + g) n = CohomologyMaps.map F P Q f n + CohomologyMaps.map F P Q g n := by
  rw [map_eq F P Q (f + g)
    (ProjectiveResolution.lift f P Q + ProjectiveResolution.lift g P Q)
    (by simp [Preadditive.add_comp, Preadditive.comp_add]) n]
  simp only [IntegralComparison.ProjectiveResolution.HomNaturality.map, op_add, Functor.map_add,
    HomologicalComplex.homologyMap_add, CohomologyMaps.map]

theorem map_sum {M N : C} (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    {ι : Type*} (t : Finset ι) (f : ι → (M ⟶ N)) (n : ℕ) :
    CohomologyMaps.map F P Q (∑ i ∈ t, f i) n = ∑ i ∈ t, CohomologyMaps.map F P Q (f i) n := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih => simp [Finset.sum_insert ha, CohomologyMaps.map_add, ih]

section Linear
variable (R : Type*) [CommRing R] [Linear R D]

theorem homologyMap_smul {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex D c} (a : K ⟶ L) (r : R) (i : ι) :
    HomologicalComplex.homologyMap (r • a) i = r • HomologicalComplex.homologyMap a i := by
  dsimp [HomologicalComplex.homologyMap]
  rw [← ShortComplex.homologyMap_smul]
  rfl

end Linear

variable (R : Type u) [CommRing R] (T : ModuleCat.{u} R)

abbrev homFunctor := (linearYoneda R (ModuleCat.{u} R)).obj T

theorem complexMap_smul {K L : ChainComplex (ModuleCat.{u} R) ℕ}
    (a : K ⟶ L) (r : R) :
    (IntegralComparison.ProjectiveResolution.HomNaturality.functor (homFunctor R T)).map (r • a).op =
      r • (IntegralComparison.ProjectiveResolution.HomNaturality.functor (homFunctor R T)).map a.op := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  change L.X i ⟶ T at q
  apply ModuleCat.hom_ext
  ext x
  change q ((r • a.f i) x) = r • q (a.f i x)
  exact q.hom.map_smul r _

theorem map_smul {M N : ModuleCat.{u} R} (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (f : M ⟶ N) (r : R) (n : ℕ) :
    CohomologyMaps.map (homFunctor R T) P Q (r • f) n = r • CohomologyMaps.map (homFunctor R T) P Q f n := by
  rw [map_eq (homFunctor R T) P Q (r • f) (r • ProjectiveResolution.lift f P Q)
    (by
      apply (ChainComplex.toSingle₀Equiv _ _).injective
      apply Subtype.ext
      change ((r • ProjectiveResolution.lift f P Q) ≫ Q.π).f 0 =
        (P.π ≫ (ChainComplex.single₀ (ModuleCat R)).map (r • f)).f 0
      simp [HomologicalComplex.comp_f, Linear.smul_comp, Linear.comp_smul]) n]
  dsimp only [IntegralComparison.ProjectiveResolution.HomNaturality.map, CohomologyMaps.map]
  rw [complexMap_smul, CohomologyMaps.homologyMap_smul]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps
