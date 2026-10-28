import Mathlib

/-! # Finite Etale -/

namespace OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale

noncomputable section

/-!
# FiniteEtale: geometric objects and their functors of points

A finite commutative group scheme is an actual group object on the spectrum
of a finite-dimensional commutative algebra. A p-divisible group is a tower
of these schemes with closed transition embeddings, the prescribed ranks,
and the defining torsion-kernel condition. That condition is tested on every
affine algebra, including nonreduced algebras.

The standard targets are explicit towers of group-valued functors on affine
algebras. Their isomorphism type is tested naturally on all these algebras;
it is not a classification of geometric points or of Dieudonné modules.
No comparison theorem or classification is assumed in these definitions.
-/

open _root_.CategoryTheory Opposite _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj

universe u

variable (k : Type u) [Field k]

/-- The affine k-scheme represented by a commutative k-algebra. -/
abbrev affine (R : CommAlgCat.{u} k) : Over (Spec (CommRingCat.of k)) :=
  (algSpec (CommRingCat.of k)).obj (op R)

/-- A finite commutative group scheme, with an affine presentation. -/
structure FiniteCommGroupScheme where
  algebra : CommAlgCat.{u} k
  finite : Module.Finite k algebra
  group : CommGrpObj (affine k algebra)

attribute [instance] FiniteCommGroupScheme.finite FiniteCommGroupScheme.group

namespace FiniteCommGroupScheme

variable {k}

abbrev scheme (G : FiniteCommGroupScheme k) := affine k G.algebra

/-- This presentation really gives a finite morphism to Spec k. -/
instance finite_morphism (G : FiniteCommGroupScheme k) : IsFinite G.scheme.hom := by
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k G.algebra)))
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr G.finite

/-- Over a field the structure morphism is flat. -/
instance flat_morphism (G : FiniteCommGroupScheme k) : Flat G.scheme.hom := by
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap k G.algebra)))
  rw [Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- All affine-valued points, retaining infinitesimal structure. -/
def points (G : FiniteCommGroupScheme k) : CommAlgCat.{u} k ⥤ CommGrpCat.{u} where
  obj R := CommGrpCat.of (affine k R ⟶ G.scheme)
  map {R S} f := CommGrpCat.ofHom {
    toFun := fun x => (algSpec (CommRingCat.of k)).map f.op ≫ x
    map_one' := MonObj.comp_one _
    map_mul' := MonObj.comp_mul _ }
  map_id R := by ext x; simp
  map_comp f g := by ext x; simp [Category.assoc]

/-- A group-scheme morphism induces a natural map on all affine points. -/
def mapPoints {G H : FiniteCommGroupScheme k} (f : G.scheme ⟶ H.scheme)
    [IsMonHom f] : G.points ⟶ H.points where
  app R := CommGrpCat.ofHom {
    toFun := fun x => x ≫ f
    map_one' := MonObj.one_comp f
    map_mul' := fun x y => MonObj.mul_comp x y f }
  naturality R S g := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    change ((algSpec (CommRingCat.of k)).map g.op ≫ x) ≫ f =
      (algSpec (CommRingCat.of k)).map g.op ≫ (x ≫ f)
    exact Category.assoc _ _ _

/-- Recover the actual scheme morphism from a natural map on every affine algebra. -/
def morphismOfPoints {G H : FiniteCommGroupScheme k} (α : G.points ⟶ H.points) :
    G.scheme ⟶ H.scheme :=
  (α.app G.algebra) (𝟙 G.scheme)

/-- A natural map on affine points is evaluation of the recovered scheme morphism. -/
theorem morphismOfPoints_apply {G H : FiniteCommGroupScheme k}
    (α : G.points ⟶ H.points) (R : CommAlgCat.{u} k)
    (x : affine k R ⟶ G.scheme) :
    (α.app R) x = x ≫ morphismOfPoints α := by
  let a : op R ⟶ op G.algebra :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage x
  have ha : (algSpec (CommRingCat.of k)).map a = x :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage x
  have h := ConcreteCategory.congr_hom (α.naturality a.unop) (𝟙 G.scheme)
  change (α.app R) ((algSpec (CommRingCat.of k)).map a ≫ 𝟙 G.scheme) =
    (algSpec (CommRingCat.of k)).map a ≫ morphismOfPoints α at h
  simpa only [ha, Category.comp_id] using h

/-- An isomorphism on all affine-valued points gives an actual scheme isomorphism.
This rules out the loss of infinitesimal information caused by using only k-points. -/
def schemeIsoOfPoints {G H : FiniteCommGroupScheme k} (e : G.points ≅ H.points) :
    G.scheme ≅ H.scheme where
  hom := morphismOfPoints e.hom
  inv := morphismOfPoints e.inv
  hom_inv_id := by
    rw [← morphismOfPoints_apply e.inv G.algebra (morphismOfPoints e.hom)]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app e.hom_inv_id G.algebra)
      (𝟙 G.scheme)
  inv_hom_id := by
    rw [← morphismOfPoints_apply e.hom H.algebra (morphismOfPoints e.inv)]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app e.inv_hom_id H.algebra)
      (𝟙 H.scheme)

end FiniteCommGroupScheme

/-- A tower of affine group functors, with its actual transition maps. -/
structure GroupTower where
  level : ℕ → CommAlgCat.{u} k ⥤ CommGrpCat.{u}
  inclusion : ∀ n, level n ⟶ level (n + 1)

/-- An isomorphism of towers is natural in every algebra and commutes with
the inclusions at every level. -/
structure GroupTower.Iso (G H : GroupTower k) where
  levelIso : ∀ n, G.level n ≅ H.level n
  compatibility : ∀ n,
    G.inclusion n ≫ (levelIso (n + 1)).hom =
      (levelIso n).hom ≫ H.inclusion n

/-- The standard inductive-system definition of a p-divisible group of height h.
Finite flatness is proved above, rather than supplied as an unexplained model.
The image/kernel equality is evaluated on all affine test schemes. -/
structure PDivisibleGroup (p h : ℕ) where
  level : ℕ → FiniteCommGroupScheme k
  inclusion : ∀ n, (level n).scheme ⟶ (level (n + 1)).scheme
  inclusion_hom : ∀ n, IsMonHom (inclusion n)
  inclusion_closed : ∀ n, IsClosedImmersion (inclusion n).left
  rank : ∀ n, Module.finrank k (level n).algebra = p ^ (n * h)
  kernel : ∀ n (R : CommAlgCat.{u} k) (x : affine k R ⟶ (level (n + 1)).scheme),
    (∃ y : affine k R ⟶ (level n).scheme, y ≫ inclusion n = x) ↔ x ^ (p ^ n) = 1

attribute [instance] PDivisibleGroup.inclusion_hom PDivisibleGroup.inclusion_closed

/-- The functor-of-points tower of an actual p-divisible group. -/
def PDivisibleGroup.points {p h : ℕ} (G : PDivisibleGroup k p h) : GroupTower k where
  level n := (G.level n).points
  inclusion n := FiniteCommGroupScheme.mapPoints (G.inclusion n)

/-- The defining kernel condition implies that every level is killed by p^n. -/
theorem PDivisibleGroup.annihilated {p h : ℕ} (G : PDivisibleGroup k p h)
    (n : ℕ) (R : CommAlgCat.{u} k) (x : affine k R ⟶ (G.level n).scheme) :
    x ^ (p ^ n) = 1 := by
  have : Mono (G.inclusion n).left := inferInstance
  have : Mono (G.inclusion n) := Over.mono_of_mono_left (G.inclusion n)
  apply (cancel_mono (G.inclusion n)).mp
  rw [MonObj.pow_comp, MonObj.one_comp]
  exact (G.kernel n R _).mp ⟨x, rfl⟩

/-- The cyclic transition j mod p^n ↦ p*j mod p^(n+1). -/
def cyclicInclusion (p n : ℕ) : ZMod (p ^ n) →+ ZMod (p ^ (n + 1)) :=
  ZMod.lift (p ^ n) ⟨p • Int.castAddHom (ZMod (p ^ (n + 1))), by
    simp only [AddMonoidHom.nsmul_apply, Int.coe_castAddHom, Int.cast_natCast]
    rw [nsmul_eq_mul, ← Nat.cast_mul, ← pow_succ']
    exact ZMod.natCast_self _⟩

@[simp]
theorem cyclicInclusion_intCast (p n : ℕ) (z : ℤ) :
    cyclicInclusion p n (z : ZMod (p ^ n)) = p • (z : ZMod (p ^ (n + 1))) := by
  simp [cyclicInclusion]

/-- The cyclic transition is an actual injection. -/
theorem cyclicInclusion_injective (p n : ℕ) (hp : p ≠ 0) :
    Function.Injective (cyclicInclusion p n) := by
  apply (ZMod.lift_injective (p ^ n)).mpr
  intro z hz
  have hz' : (((p : ℤ) * z : ℤ) : ZMod (p ^ (n + 1))) = 0 := by
    simpa [nsmul_eq_mul] using hz
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz' ⊢
  simpa only [Nat.cast_pow, Nat.cast_mul, pow_succ', mul_dvd_mul_iff_left (by exact_mod_cast hp :
    (p : ℤ) ≠ 0)] using hz'

/-- The constant cyclic group scheme on affine points. Locally constant
functions are necessary for disconnected test schemes. -/
def etaleLevel (p n : ℕ) : CommAlgCat.{u} k ⥤ CommGrpCat.{u} where
  obj R := CommGrpCat.of (LocallyConstant (PrimeSpectrum R) (Multiplicative (ZMod (p ^ n))))
  map {R S} f := CommGrpCat.ofHom (LocallyConstant.comapMonoidHom
    ⟨PrimeSpectrum.comap f.hom.toRingHom, PrimeSpectrum.continuous_comap _⟩)
  map_id R := by ext x y; simp [PrimeSpectrum.comap_id]
  map_comp f g := by ext x y; rfl

/-- The standard étale tower (Z/p^n)_k, denoted Q_p/Z_p. -/
def etaleTower (p : ℕ) : GroupTower k where
  level := etaleLevel k p
  inclusion n := {
    app R := CommGrpCat.ofHom (LocallyConstant.mapMonoidHom
      (AddMonoidHom.toMultiplicative (cyclicInclusion p n)))
    naturality R S f := by ext x; rfl }

/-- The multiplicative finite group functor on all affine algebras. -/
def multiplicativeLevel (p n : ℕ) : CommAlgCat.{u} k ⥤ CommGrpCat.{u} where
  obj R := CommGrpCat.of (rootsOfUnity (p ^ n) R)
  map {R S} f := CommGrpCat.ofHom (restrictRootsOfUnity f.hom (p ^ n))
  map_id R := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- The standard tower μ_(p^n), denoted μ_(p^∞). -/
def multiplicativeTower (p : ℕ) : GroupTower k where
  level := multiplicativeLevel k p
  inclusion n := {
    app R := CommGrpCat.ofHom (Subgroup.inclusion
      (rootsOfUnity_le_of_dvd (M := R) (pow_dvd_pow p (Nat.le_succ n))))
    naturality R S f := by ext x; rfl }

/-- The multiplicative transition is an actual injection on every affine algebra. -/
theorem multiplicativeTower_injective (p n : ℕ) (R : CommAlgCat.{u} k) :
    Function.Injective ((multiplicativeTower k p).inclusion n |>.app R) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : rootsOfUnity (p ^ (n + 1)) R => (z : Rˣ)) h

/-- The multiplicative tower has the required torsion kernels on all algebras. -/
theorem multiplicativeTower_kernel (p n : ℕ) (R : CommAlgCat.{u} k)
    (x : ((multiplicativeTower k p).level (n + 1)).obj R) :
    (∃ y : ((multiplicativeTower k p).level n).obj R,
      ((multiplicativeTower k p).inclusion n).app R y = x) ↔ x ^ (p ^ n) = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    exact (mem_rootsOfUnity _ _).mp y.property
  · intro hx
    refine ⟨⟨x.val, ?_⟩, rfl⟩
    exact (mem_rootsOfUnity _ _).mpr (congrArg Subtype.val hx)

/-- The étale transition is an actual injection on every affine algebra. -/
theorem etaleTower_injective (p n : ℕ) (hp : p ≠ 0) (R : CommAlgCat.{u} k) :
    Function.Injective ((etaleTower k p).inclusion n |>.app R) := by
  intro x y h
  apply LocallyConstant.ext
  intro z
  apply cyclicInclusion_injective p n hp
  exact congrArg (fun f : LocallyConstant (PrimeSpectrum R)
    (Multiplicative (ZMod (p ^ (n + 1)))) => f z) h

end

end OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale
