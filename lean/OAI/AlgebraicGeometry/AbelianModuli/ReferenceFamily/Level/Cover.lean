import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Data.ZMod.Basic

/-! # Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Cover.LevelCover

noncomputable section

/-! Construction of the added-level frame locus as an actual open
subscheme of a finite product of the scheme-theoretic N-torsion.
No representability or existence theorem for level structures is assumed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (N : ℕ)

def torsion : Over S := equalizer ((𝟙 A.scheme) ^ N) (1 : A.scheme ⟶ A.scheme)

def torsionInclusion : torsion A N ⟶ A.scheme :=
  equalizer.ι ((𝟙 A.scheme) ^ N) (1 : A.scheme ⟶ A.scheme)

theorem torsionInclusion_pow : torsionInclusion A N ^ N = 1 := by
  convert! (show (equalizer.ι ((𝟙 A.scheme) ^ N) (1 : A.scheme ⟶ A.scheme)) ^ N = 1 from
    (by simpa only [MonObj.comp_pow, Category.comp_id, MonObj.comp_one] using
      equalizer.condition ((𝟙 A.scheme) ^ N) (1 : A.scheme ⟶ A.scheme)))

/-- The torsion scheme represents exactly the points annihilated by N. -/
def torsionPointsEquiv (T : Over S) :
    (T ⟶ torsion A N) ≃ {x : T ⟶ A.scheme // x ^ N = 1} where
  toFun f := ⟨f ≫ torsionInclusion A N, by
    rw [← MonObj.comp_pow, torsionInclusion_pow, MonObj.comp_one]⟩
  invFun x := equalizer.lift x.val (by
    simpa only [MonObj.comp_pow, Category.comp_id, MonObj.comp_one] using x.property)
  left_inv f := by
    apply equalizer.hom_ext
    exact equalizer.lift_ι _ _
  right_inv x := Subtype.ext (equalizer.lift_ι _ _)

def torsionTuples : Over S := Limits.piObj (fun _ : Fin (2 * g) => torsion A N)

def coordinate (i : Fin (2 * g)) : torsionTuples A N ⟶ A.scheme :=
  Pi.π (fun _ : Fin (2 * g) => torsion A N) i ≫ torsionInclusion A N

theorem coordinate_pow (i : Fin (2 * g)) : coordinate A N i ^ N = 1 := by
  change (Pi.π (fun _ : Fin (2 * g) => torsion A N) i ≫ torsionInclusion A N) ^ N = 1
  rw [← MonObj.comp_pow, torsionInclusion_pow, MonObj.comp_one]

/-- Evaluate a relation among the chosen torsion generators. -/
def relation (c : Fin (2 * g) → ZMod N) : torsionTuples A N ⟶ A.scheme :=
  ∏ i : Fin (2 * g), coordinate A N i ^ (c i).val

def relationZero (c : Fin (2 * g) → ZMod N) : Over S :=
  equalizer (relation A N c) (1 : torsionTuples A N ⟶ A.scheme)

def relationZeroInclusion (c : Fin (2 * g) → ZMod N) :
    relationZero A N c ⟶ torsionTuples A N :=
  equalizer.ι (relation A N c) (1 : torsionTuples A N ⟶ A.scheme)

instance relationZero_closed (c : Fin (2 * g) → ZMod N) :
    IsClosedImmersion (relationZeroInclusion A N c).left :=
  isClosedImmersion_equalizer_ι_left _ _

def relationNonzero (c : Fin (2 * g) → ZMod N) : (torsionTuples A N).left.Opens :=
  ⟨(Set.range (relationZeroInclusion A N c).left)ᶜ,
    (relationZeroInclusion A N c).left.isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The actual open locus on which no nonzero relation vanishes. -/
def frameOpen : (torsionTuples A N).left.Opens :=
  ⨅ (c : Fin (2 * g) → ZMod N) (_ : c ≠ 0), relationNonzero A N c

def frameScheme : Over S :=
  Over.mk ((frameOpen A N).ι ≫ (torsionTuples A N).hom)

/-- Forget the new frame and recover its tuple of torsion points. -/
def frameInclusion : frameScheme A N ⟶ torsionTuples A N :=
  Over.homMk (frameOpen A N).ι rfl

instance frameInclusion_open : IsOpenImmersion (frameInclusion A N).left :=
  inferInstanceAs (IsOpenImmersion (frameOpen A N).ι)

theorem frame_coordinate_pow (i : Fin (2 * g)) :
    (frameInclusion A N ≫ coordinate A N i) ^ N = 1 := by
  rw [← MonObj.comp_pow, coordinate_pow, MonObj.comp_one]

/-- Every geometric point of the constructed open locus avoids all the
forbidden relation subschemes. -/
theorem frame_point_avoids_relation (x : (frameScheme A N).left)
    (c : Fin (2 * g) → ZMod N) (hc : c ≠ 0) :
    (frameInclusion A N).left x ∉ Set.range (relationZeroInclusion A N c).left := by
  have hx : (frameInclusion A N).left x ∈ frameOpen A N := by
    change (frameOpen A N).ι x ∈ (frameOpen A N : Set (torsionTuples A N).left)
    rw [← Scheme.Opens.range_ι]
    exact Set.mem_range_self x
  have hle : frameOpen A N ≤ relationNonzero A N c :=
    iInf_le_of_le c (iInf_le _ hc)
  exact hle hx

/-- The universal torsion generators have no nonzero relation on any
nonempty test scheme mapping to the frame locus. -/
theorem frame_relations_nonzero (T : Over S) [Nonempty T.left]
    (f : T ⟶ frameScheme A N) (c : Fin (2 * g) → ZMod N) (hc : c ≠ 0) :
    (f ≫ frameInclusion A N) ≫ relation A N c ≠ 1 := by
  intro h
  let t : T.left := Classical.choice inferInstance
  let q := f ≫ frameInclusion A N
  have hq : q ≫ relation A N c = q ≫ (1 : torsionTuples A N ⟶ A.scheme) := by
    rw [MonObj.comp_one]
    exact h
  apply frame_point_avoids_relation A N (f.left t) c hc
  refine ⟨(equalizer.lift q hq).left t, ?_⟩
  exact congrArg (fun m : T ⟶ torsionTuples A N => m.left t)
    (equalizer.lift_ι q hq)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.Cover.LevelCover
