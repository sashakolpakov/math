import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.LevelFamilies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionCoefficientGroupIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.FrameRestriction

/-! # Divisor Level Int -/

namespace OAI.AlgebraicGeometry.AbelianModuli

noncomputable section

/-! Restriction of an actual full level at `L * k` to the divisor `L`.
The construction uses the subgroup killed by `L`, so it is valid on
all test schemes, including disconnected and nonreduced schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace ReferenceFamily.DivisorLevelInt.DivisorLevel

variable (L k : ℕ)

/-- The inclusion of the `L`-torsion coefficients in the `L * k` coefficients. -/
def coefficient : ZMod L →+ ZMod (L * k) :=
  HilbertConstruction.TorsionCoefficientGroupIsomorphism.torsionCoefficientHom L (k : ZMod (L * k)) (by
    simp only [zsmul_eq_mul, Int.cast_natCast]
    rw [← Nat.cast_mul]
    exact ZMod.natCast_self (L * k))

theorem coefficient_intCast (a : ℤ) :
    coefficient L k (a : ZMod L) = (a : ZMod (L * k)) * k := by
  simp only [coefficient, HilbertConstruction.TorsionCoefficientGroupIsomorphism.torsionCoefficientHom_intCast, zsmul_eq_mul]

theorem coefficient_injective (hk : 0 < k) : Function.Injective (coefficient L k) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  rw [coefficient_intCast] at hx
  have h : (L : ℤ) * k ∣ a * k := by
    have h' : ((a * k : ℤ) : ZMod (L * k)) = 0 := by
      simpa only [Int.cast_mul, Int.cast_natCast] using hx
    simpa only [Nat.cast_mul] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h'
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    ((mul_dvd_mul_iff_right (by exact_mod_cast Nat.ne_of_gt hk)).mp h)

theorem coefficient_killed (x : ZMod L) : L • coefficient L k x = 0 := by
  rw [← map_nsmul]
  have h : L • x = 0 := by
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [h, map_zero]

theorem coefficient_range (hL : 0 < L) (x : ZMod (L * k)) :
    (∃ y, coefficient L k y = x) ↔ L • x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact coefficient_killed L k y
  · intro hx
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
    have h : (L : ℤ) * k ∣ (L : ℤ) * a := by
      have h' : (((L : ℤ) * a : ℤ) : ZMod (L * k)) = 0 := by
        simpa only [Int.cast_mul, Int.cast_natCast, nsmul_eq_mul] using hx
      simpa only [Nat.cast_mul] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h'
    obtain ⟨b, hb⟩ := (mul_dvd_mul_iff_left (by exact_mod_cast Nat.ne_of_gt hL)).mp h
    refine ⟨(b : ZMod L), ?_⟩
    rw [coefficient_intCast, hb, Int.cast_mul, Int.cast_natCast]
    exact mul_comm _ _

variable (g : ℕ)

def labels : Multiplicative (Fin (2 * g) → ZMod L) →*
    Multiplicative (Fin (2 * g) → ZMod (L * k)) :=
  { toFun := fun x => Multiplicative.ofAdd (fun i => coefficient L k (x.toAdd i))
    map_one' := by
      ext i
      exact map_zero (coefficient L k)
    map_mul' := by
      intro x y
      ext i
      exact map_add (coefficient L k) (x.toAdd i) (y.toAdd i) }

theorem labels_injective (hk : 0 < k) : Function.Injective (labels L k g) := by
  intro x y h
  change x.toAdd = y.toAdd
  funext i
  apply coefficient_injective L k hk
  exact congrArg (fun z => z.toAdd i) h

theorem labels_killed (x : Multiplicative (Fin (2 * g) → ZMod L)) :
    labels L k g x ^ L = 1 := by
  change (labels L k g x ^ L).toAdd = (1 : Multiplicative _).toAdd
  funext i
  exact coefficient_killed L k (x.toAdd i)

theorem labels_range (hL : 0 < L) (x : Multiplicative (Fin (2 * g) → ZMod (L * k))) :
    (∃ y, labels L k g y = x) ↔ x ^ L = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact labels_killed L k g y
  · intro hx
    have hi (i : Fin (2 * g)) : ∃ y, coefficient L k y = x.toAdd i :=
      (coefficient_range L k hL _).mpr (congrArg (fun z => z.toAdd i) hx)
    choose y hy using hi
    refine ⟨Multiplicative.ofAdd y, ?_⟩
    change (labels L k g (Multiplicative.ofAdd y)).toAdd = x.toAdd
    exact funext hy

variable {X : Type*} [TopologicalSpace X]

def sections : LocallyConstant X (Multiplicative (Fin (2 * g) → ZMod L)) →*
    LocallyConstant X (Multiplicative (Fin (2 * g) → ZMod (L * k))) :=
  LocallyConstant.mapMonoidHom (labels L k g)

theorem sections_injective (hk : 0 < k) :
    Function.Injective (sections L k g (X := X)) := by
  intro x y h
  apply LocallyConstant.ext
  intro t
  exact labels_injective L k g hk (congrArg (fun z => z t) h)

theorem sections_killed (x : LocallyConstant X (Multiplicative (Fin (2 * g) → ZMod L))) :
    sections L k g x ^ L = 1 := by
  apply LocallyConstant.ext
  intro t
  exact labels_killed L k g (x t)

theorem sections_range (hL : 0 < L)
    (x : LocallyConstant X (Multiplicative (Fin (2 * g) → ZMod (L * k)))) :
    (∃ y, sections L k g y = x) ↔ x ^ L = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact sections_killed L k g y
  · intro hx
    let inv := Function.invFun (labels L k g)
    refine ⟨x.map inv, ?_⟩
    apply LocallyConstant.ext
    intro t
    change labels L k g (Function.invFun (labels L k g) (x t)) = x t
    obtain ⟨y, hy⟩ := (labels_range L k g hL (x t)).mpr (congrArg (fun z => z t) hx)
    rw [← hy]
    exact Function.apply_invFun_apply

end ReferenceFamily.DivisorLevelInt.DivisorLevel

section

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DivisorLevelInt.DivisorLevel

universe u

variable {S : Scheme.{u}} {g L k : ℕ} {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S}

/-- Restrict a full-level basis to the subgroup killed by the divisor. -/
def HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.divisorComponent (α : A.FullLevel (L * k)) (T : Over S) :
    LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod L)) →*
      A.torsionPoints L T where
  toFun c := ⟨(α.hom.app (.op T) (ReferenceFamily.DivisorLevelInt.DivisorLevel.sections L k g c)).val, by
    have h : (α.hom.app (.op T) (ReferenceFamily.DivisorLevelInt.DivisorLevel.sections L k g c)) ^ L = 1 := by
      exact ((α.hom.app (.op T)).hom.map_pow _ L).symm.trans
        ((congrArg (α.hom.app (.op T)).hom (ReferenceFamily.DivisorLevelInt.DivisorLevel.sections_killed L k g c)).trans
          (α.hom.app (.op T)).hom.map_one)
    exact congrArg (fun z : A.torsionPoints (L * k) T => z.val) h⟩
  map_one' := by
    apply Subtype.ext
    change (α.hom.app (.op T) (ReferenceFamily.DivisorLevelInt.DivisorLevel.sections L k g 1)).val = _
    exact congrArg (fun z : A.torsionPoints (L * k) T => z.val)
      ((congrArg (α.hom.app (.op T)).hom (ReferenceFamily.DivisorLevelInt.DivisorLevel.sections L k g).map_one).trans
        (α.hom.app (.op T)).hom.map_one)
  map_mul' c d := by
    apply Subtype.ext
    change (α.hom.app (.op T) (ReferenceFamily.DivisorLevelInt.DivisorLevel.sections L k g (c * d))).val = _
    exact congrArg (fun z : A.torsionPoints (L * k) T => z.val)
      ((congrArg (α.hom.app (.op T)).hom ((ReferenceFamily.DivisorLevelInt.DivisorLevel.sections L k g).map_mul c d)).trans
        ((α.hom.app (.op T)).hom.map_mul _ _))

theorem HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.divisorComponent_bijective (α : A.FullLevel (L * k))
    (hL : 0 < L) (hk : 0 < k) (T : Over S) :
    Function.Bijective (α.divisorComponent T) := by
  constructor
  · intro c d h
    apply ReferenceFamily.DivisorLevelInt.DivisorLevel.sections_injective L k g hk
    apply (α.app (.op T)).groupIsoToMulEquiv.injective
    exact Subtype.ext (congrArg (fun z : A.torsionPoints L T => z.val) h)
  · intro y
    let yN : A.torsionPoints (L * k) T := ⟨y.val, by
      change y.val ^ (L * k) = 1
      rw [pow_mul, (HilbertConstruction.Abelian.Schemes.AbelianScheme.mem_torsionPoints A L T y.val).mp y.property, one_pow]⟩
    have hyN : yN ^ L = 1 := Subtype.ext y.property
    let x := α.inv.app (.op T) yN
    have hx : x ^ L = 1 := by
      change (α.inv.app (.op T) yN) ^ L = 1
      exact ((α.inv.app (.op T)).hom.map_pow yN L).symm.trans
        ((congrArg (α.inv.app (.op T)).hom hyN).trans (α.inv.app (.op T)).hom.map_one)
    obtain ⟨c, hc⟩ := (ReferenceFamily.DivisorLevelInt.DivisorLevel.sections_range L k g hL x).mpr hx
    refine ⟨c, Subtype.ext ?_⟩
    change (α.hom.app (.op T) (ReferenceFamily.DivisorLevelInt.DivisorLevel.sections L k g c)).val = y.val
    rw [hc]
    exact congrArg Subtype.val ((α.app (.op T)).groupIsoToMulEquiv.apply_symm_apply yN)

/-- A full `L * k` level canonically determines a full `L` level. -/
def HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.divisor (α : A.FullLevel (L * k)) (hL : 0 < L) (hk : 0 < k) : A.FullLevel L :=
  NatIso.ofComponents
    (fun T => MulEquiv.toGrpIso
      (MulEquiv.ofBijective (α.divisorComponent T.unop)
        (α.divisorComponent_bijective hL hk T.unop)))
    (by
      intro T U f
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro c
      apply Subtype.ext
      exact congrArg (fun z : A.torsionPoints (L * k) U.unop => z.val)
        (ConcreteCategory.congr_hom (α.hom.naturality f) (ReferenceFamily.DivisorLevelInt.DivisorLevel.sections L k g c)))

theorem HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.divisor_basis (α : A.FullLevel (L * k)) (hL : 0 < L) (hk : 0 < k)
    (T : Over S) (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod L))) :
    ((α.divisor hL hk).hom.app (.op T) c).val =
      (α.hom.app (.op T) (ReferenceFamily.DivisorLevelInt.DivisorLevel.sections L k g c)).val := rfl

theorem HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.divisor_pullback {S' : Scheme.{u}} (α : A.FullLevel (L * k))
    (hL : 0 < L) (hk : 0 < k) (f : S' ⟶ S) :
    (α.divisor hL hk).pullback f = (α.pullback f).divisor hL hk := by
  apply HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro T c
  rfl

theorem HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.divisor_transport {B : HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (α : A.FullLevel (L * k))
    (hL : 0 < L) (hk : 0 < k) (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    (α.divisor hL hk).transport e = (α.transport e).divisor hL hk := by
  apply HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.ext_basis
  intro T c
  rfl

theorem HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.divisor_restrict {T U : Over S} (α : (A.pullback U.hom).FullLevel (L * k))
    (hL : 0 < L) (hk : 0 < k) (f : T ⟶ U) :
    (α.divisor hL hk).restrict f = (α.restrict f).divisor hL hk := by
  simp only [HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.restrict, HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.divisor_pullback, HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.divisor_transport]

end

namespace ReferenceFamily.DivisorLevelInt.LevelCover

variable {S : Scheme.{0}} {g L k : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  [NeZero L] [NeZero k]

/-- Divisor restriction is natural for the actual full-level family functors. -/
def divisorLevelTransformation :
    Frame.FrameRestriction.LevelCover.fullLevelFamilyFunctor A (N := L * k) ⟶ Frame.FrameRestriction.LevelCover.fullLevelFamilyFunctor A (N := L) where
  app T := TypeCat.ofHom (fun (α : (A.pullback T.unop.hom).FullLevel (L * k)) =>
    α.divisor (A := A.pullback T.unop.hom) (L := L) (k := k)
      (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.pos_of_ne_zero (NeZero.ne k)))
  naturality {T U} f := by
    apply ConcreteCategory.ext_apply (FC := TypeCat.Fun) (CC := fun X : Type 1 => X)
    intro α
    exact (HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.divisor_restrict (A := A) α (Nat.pos_of_ne_zero (NeZero.ne L))
      (Nat.pos_of_ne_zero (NeZero.ne k)) f.unop).symm

end ReferenceFamily.DivisorLevelInt.LevelCover

end

end OAI.AlgebraicGeometry.AbelianModuli
