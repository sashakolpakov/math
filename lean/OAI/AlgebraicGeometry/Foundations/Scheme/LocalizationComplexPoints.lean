import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Basic.Complex.Basic

/-! # Localization Complex Points -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic

noncomputable section

/-!
# Field-valued points of a principal localization

Restriction along `A → A[g⁻¹]` identifies field-valued characters of the
localization with characters of `A` at which `g` does not vanish. The inverse
is the universal-property extension, with an explicit fractional evaluation
formula and compatibility with algebra morphisms.
-/

universe u v w

variable {K : Type u} {S : Type v}
variable [Field K] [CommRing S] [Algebra K S]

/-- Extend a field-valued point to a principal localization when the inverted
element does not vanish at that point. -/
def localizePoint (x : S →ₐ[K] K) (g : S) (hg : x g ≠ 0) :
    Localization.Away g →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom (S := Localization.Away g) (f := x) g
    (isUnit_iff_ne_zero.mpr hg)

@[simp]
theorem localizePoint_algebraMap (x : S →ₐ[K] K) (g : S) (hg : x g ≠ 0)
    (a : S) : localizePoint x g hg (algebraMap S (Localization.Away g) a) = x a := by
  simp [localizePoint]

/-- The localized character restricts to the original character. -/
@[simp]
theorem localizePoint_comp (x : S →ₐ[K] K) (g : S) (hg : x g ≠ 0) :
    (localizePoint x g hg).comp (Algebra.algHom K S (Localization.Away g)) = x := by
  ext a
  exact localizePoint_algebraMap x g hg a

/-- A character extension to this localization is unique. -/
theorem localizePoint_unique (x : S →ₐ[K] K) (g : S) (hg : x g ≠ 0)
    (y : Localization.Away g →ₐ[K] K)
    (hy : y.comp (Algebra.algHom K S (Localization.Away g)) = x) :
    y = localizePoint x g hg := by
  apply IsLocalization.algHom_ext (Submonoid.powers g)
  exact hy.trans (localizePoint_comp x g hg).symm

/-- Restricting a character from a principal localization gives a character
at which the inverted element is nonzero. -/
def localizationPointRestrict (g : S) (y : Localization.Away g →ₐ[K] K) :
    {x : S →ₐ[K] K // x g ≠ 0} :=
  ⟨y.comp (Algebra.algHom K S (Localization.Away g)), by
    exact isUnit_iff_ne_zero.mp
      ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).map y)⟩

/-- Field-valued points of `A[g⁻¹]` are exactly points of `A` where `g ≠ 0`. -/
def localizationPointEquiv (g : S) :
    (Localization.Away g →ₐ[K] K) ≃ {x : S →ₐ[K] K // x g ≠ 0} where
  toFun := localizationPointRestrict g
  invFun x := localizePoint x.val g x.property
  left_inv y := by
    symm
    apply localizePoint_unique
    rfl
  right_inv x := by
    apply Subtype.ext
    exact localizePoint_comp x.val g x.property

@[simp]
theorem localizationPointEquiv_apply_val (g : S)
    (y : Localization.Away g →ₐ[K] K) :
    (localizationPointEquiv g y).val =
      y.comp (Algebra.algHom K S (Localization.Away g)) := rfl

@[simp]
theorem localizationPointEquiv_symm_apply (g : S)
    (x : {x : S →ₐ[K] K // x g ≠ 0}) :
    (localizationPointEquiv g).symm x = localizePoint x.val g x.property := rfl

/-- Evaluating an extended character is a quotient of two evaluations on the
original algebra. The numerator and exponent depend only on the localized element. -/
theorem localizePoint_eq_div_sec (x : S →ₐ[K] K) (g : S) (hg : x g ≠ 0)
    (z : Localization.Away g) :
    localizePoint x g hg z =
      x (IsLocalization.Away.sec g z).1 / (x g) ^ (IsLocalization.Away.sec g z).2 := by
  apply (eq_div_iff (pow_ne_zero _ hg)).mpr
  have h := congrArg (localizePoint x g hg)
    (IsLocalization.Away.sec_spec (S := Localization.Away g) g z)
  simpa only [map_mul, localizePoint_algebraMap, map_pow] using h

/-- The inverse point equivalence has an explicit fractional evaluation formula. -/
theorem localizationPointEquiv_symm_apply_eval (g : S)
    (x : {x : S →ₐ[K] K // x g ≠ 0}) (z : Localization.Away g) :
    (localizationPointEquiv g).symm x z =
      x.val (IsLocalization.Away.sec g z).1 /
        (x.val g) ^ (IsLocalization.Away.sec g z).2 :=
  localizePoint_eq_div_sec x.val g x.property z

variable {T : Type w} [CommRing T] [Algebra K T]

/-- The induced algebra map on principal localizations agrees with the
original algebra map on numerators. -/
@[simp]
theorem awayMap_algebraMap (f : S →ₐ[K] T) (g a : S) :
    Localization.awayMapₐ f g (algebraMap S (Localization.Away g) a) =
      algebraMap T (Localization.Away (f g)) (f a) := by
  simp [Localization.awayMapₐ, IsLocalization.Away.mapₐ, IsLocalization.Away.map]

/-- Extending a point to a principal localization commutes with pullback
along an algebra morphism. -/
theorem localizePoint_natural (f : S →ₐ[K] T) (g : S)
    (y : T →ₐ[K] K) (hy : y (f g) ≠ 0) :
    (localizePoint y (f g) hy).comp (Localization.awayMapₐ f g) =
      localizePoint (y.comp f) g hy := by
  apply localizePoint_unique
  ext a
  change localizePoint y (f g) hy
    (Localization.awayMapₐ f g (algebraMap S (Localization.Away g) a)) = y (f a)
  rw [awayMap_algebraMap, localizePoint_algebraMap]

/-- Restriction of localized points commutes with algebra morphisms. -/
theorem localizationPointEquiv_natural (f : S →ₐ[K] T) (g : S)
    (y : Localization.Away (f g) →ₐ[K] K) :
    (localizationPointEquiv g (y.comp (Localization.awayMapₐ f g))).val =
      ((localizationPointEquiv (f g) y).val).comp f := by
  ext a
  change y (Localization.awayMapₐ f g (algebraMap S (Localization.Away g) a)) =
    y (algebraMap T (Localization.Away (f g)) (f a))
  rw [awayMap_algebraMap]

/-- The complex specialization used for ordinary affine complex-point charts. -/
abbrev localizationComplexPointsEquiv {A : Type v} [CommRing A] [Algebra ℂ A]
    (g : A) :
    (Localization.Away g →ₐ[ℂ] ℂ) ≃ {x : A →ₐ[ℂ] ℂ // x g ≠ 0} :=
  localizationPointEquiv g

end

end OAI.AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic
