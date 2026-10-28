import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Specialization
import Mathlib.NumberTheory.NumberField.Basic

/-! # Open -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Open

noncomputable section

/-!
An SpreadingOut model preserves surjectivity of the maps in the original diagram.
The two arithmetic-base structures below reproduce the data in SpreadingOut. No
generation or surjectivity condition is included in them.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

abbrev fieldBase (K : Type u) [Field K] : Scheme.{u} :=
  Spec (CommRingCat.of K)

/-- The arithmetic open and its generic point, as specified by SpreadingOut. -/
structure ArithmeticOpen (K : Type u) [Field K] [NumberField K] where
  U : (Spec (CommRingCat.of (NumberField.RingOfIntegers K))).Opens
  finite_complement :
    ((U : Set (Spec
      (CommRingCat.of (NumberField.RingOfIntegers K))))ᶜ).Finite
  generic : fieldBase K ⟶ U.toScheme
  generic_eq :
    generic ≫ U.ι =
      Spec.map (CommRingCat.ofHom
        (algebraMap (NumberField.RingOfIntegers K) K))

/-- A finite extension, retaining the same data as SpreadingOut. -/
structure FiniteNumberFieldExtension
    (K : Type u) [Field K] [NumberField K] where
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra K carrier]
  [finite : FiniteDimensional K carrier]
  [numberField : NumberField carrier]

attribute [instance] FiniteNumberFieldExtension.field
  FiniteNumberFieldExtension.algebra FiniteNumberFieldExtension.finite
  FiniteNumberFieldExtension.numberField

/-- The specified generic point is dominant in the arithmetic open. -/
theorem ArithmeticOpen.generic_dominant
    {K : Type u} [Field K] [NumberField K] (B : ArithmeticOpen K) :
    IsDominant B.generic := by
  have hspec : IsDominant
      (Spec.map (CommRingCat.ofHom
        (algebraMap (NumberField.RingOfIntegers K) K))) := by
    constructor
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    intro x hx
    have hx0 : x = 0 := NumberField.RingOfIntegers.coe_injective
      (show algebraMap (NumberField.RingOfIntegers K) K x =
        algebraMap (NumberField.RingOfIntegers K) K 0 from
          (RingHom.mem_ker.mp hx).trans (map_zero _).symm)
    exact hx0 ▸ Ideal.zero_mem _
  let : IsDominant (B.generic ≫ B.U.ι) := B.generic_eq.symm ▸ hspec
  exact IsDominant.of_comp_of_isOpenImmersion B.generic B.U.ι

/-- Surjectivity is unchanged by generic-fiber identifications in a
commuting square, and therefore holds throughout a smooth proper SpreadingOut model. -/
theorem model_map_surjective
    {K : Type u} [Field K] [NumberField K]
    (L : FiniteNumberFieldExtension K) (B : ArithmeticOpen L.carrier)
    {X Y : Over (fieldBase K)} (f : X ⟶ Y) [Surjective f.left]
    {MX MY : Over B.U.toScheme} (fM : MX ⟶ MY)
    [IsProper MX.hom] [IsSeparated MY.hom] [Smooth MY.hom]
    (eX : (Over.pullback B.generic).obj MX ≅
      (Over.pullback (Spec.map
        (CommRingCat.ofHom (algebraMap K L.carrier)))).obj X)
    (eY : (Over.pullback B.generic).obj MY ≅
      (Over.pullback (Spec.map
        (CommRingCat.ofHom (algebraMap K L.carrier)))).obj Y)
    (hcompatible :
      (Over.pullback B.generic).map fM ≫ eY.hom =
        eX.hom ≫ (Over.pullback (Spec.map
          (CommRingCat.ofHom (algebraMap K L.carrier)))).map f) :
    Surjective fM.left := by
  let k := Spec.map (CommRingCat.ofHom (algebraMap K L.carrier))
  let fb := ((Over.pullback k).map f).left
  let fg := ((Over.pullback B.generic).map fM).left
  have hfb : Surjective fb :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (Specialization.base_change_square k f) inferInstance
  have hleft : fg ≫ eY.hom.left = eX.hom.left ≫ fb :=
    congrArg (fun h => h.left) hcompatible
  let : IsIso eX.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map eX.hom))
  let : IsIso eY.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map eY.hom))
  have hfg : Surjective fg := by
    constructor
    intro y
    obtain ⟨x, hx⟩ := hfb.surj (eY.hom.left y)
    obtain ⟨xg, hxg⟩ := eX.hom.left.surjective x
    refine ⟨xg, eY.hom.left.isOpenEmbedding.injective ?_⟩
    calc
      eY.hom.left (fg xg) = fb (eX.hom.left xg) :=
        congrArg (fun h => h xg) hleft
      _ = eY.hom.left y := by rw [hxg, hx]
  have : IsProper (fM.left ≫ MY.hom) := by
    rw [fM.w]
    infer_instance
  have hproper : IsProper fM.left :=
    IsProper.of_comp fM.left MY.hom
  let : IsDominant B.generic := B.generic_dominant
  exact Specialization.surjective_of_dominant_base_change B.generic fM hfg

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Open
