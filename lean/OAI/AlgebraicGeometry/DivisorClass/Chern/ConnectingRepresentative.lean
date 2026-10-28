import OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence
import OAI.AlgebraicTopology.Cohomology.Singular.Representatives

/-! # Connecting Representative -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingRepresentative

noncomputable section

/-!
# ChernClass: actual cocycle representatives for the connecting map

The formula is derived from mathlib's constructed homology-sequence connecting
map. A cocycle lifts to the middle complex, its differential lifts to the first
complex, and that lift represents the actual connecting class. This fixes the
sign and avoids introducing a second boundary operation.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem cochainNext (n : ℕ) : (ComplexShape.up ℕ).next n = n + 1 :=
  (ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)

/-- A vector represented as a map out of the scalar module. -/
def pointMorphism {V : ModuleCat.{0} ℚ} (v : V) : ModuleCat.of ℚ ℚ ⟶ V :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ V v)

theorem pointMorphism_one {V : ModuleCat.{0} ℚ} (v : V) : pointMorphism v 1 = v :=
  LinearMap.toSpanSingleton_apply_one ℚ V v

/-- The categorical cycle lift of one scalar has the existing cocycle-class meaning. -/
theorem liftCyclesPoint_class (K : CochainComplex (ModuleCat.{0} ℚ) ℕ) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K n)
    (hc : pointMorphism (c : K.X n) ≫ K.d n (n + 1) = 0) :
    K.homologyπ n (K.liftCycles (pointMorphism (c : K.X n)) (n + 1) (cochainNext n) hc 1) = AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass K n c := by
  rw [AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_homologyπ]
  congr 1
  apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
  have h := ConcreteCategory.congr_hom
    (K.liftCycles_i (pointMorphism (c : K.X n)) (n + 1) (cochainNext n) hc) 1
  have h' := ConcreteCategory.congr_hom ((K.sc n).moduleCatCyclesIso_inv_iCycles) c
  change K.iCycles n (K.liftCycles (pointMorphism (c : K.X n)) (n + 1) (cochainNext n) hc 1) =
    pointMorphism (c : K.X n) 1 at h
  rw [pointMorphism_one] at h
  exact h.trans h'.symm

/-- The actual connecting map is represented by the differential of a lifted cocycle. -/
theorem connecting_class_of_lift
    (S : ShortComplex (CochainComplex (ModuleCat.{0} ℚ) ℕ)) (hS : S.ShortExact) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles S.X₃ n) (b : S.X₂.X n) (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles S.X₁ (n + 1))
    (hb : S.g.f n b = c.val) (ha : S.f.f (n + 1) a.val = S.X₂.d n (n + 1) b) :
    hS.δ n (n + 1) rfl (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass S.X₃ n c) = AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass S.X₁ (n + 1) a := by
  have hc : pointMorphism (c : S.X₃.X n) ≫ S.X₃.d n (n + 1) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change S.X₃.d n (n + 1) (pointMorphism (c : S.X₃.X n) 1) = 0
    rw [pointMorphism_one]
    exact (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff S.X₃ n c.val).mp c.property
  have hb' : pointMorphism b ≫ S.g.f n = pointMorphism (c : S.X₃.X n) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change S.g.f n (pointMorphism b 1) = pointMorphism (c : S.X₃.X n) 1
    rw [pointMorphism_one, pointMorphism_one]
    exact hb
  have ha' : pointMorphism (a : S.X₁.X (n + 1)) ≫ S.f.f (n + 1) =
      pointMorphism b ≫ S.X₂.d n (n + 1) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change S.f.f (n + 1) (pointMorphism (a : S.X₁.X (n + 1)) 1) =
      S.X₂.d n (n + 1) (pointMorphism b 1)
    rw [pointMorphism_one, pointMorphism_one]
    exact ha
  have h := ConcreteCategory.congr_hom
    (hS.δ_eq n (n + 1) rfl (pointMorphism (c : S.X₃.X n)) hc
      (pointMorphism b) hb' (pointMorphism (a : S.X₁.X (n + 1))) ha' (n + 2) (cochainNext (n + 1))) 1
  change hS.δ n (n + 1) rfl
      (S.X₃.homologyπ n (S.X₃.liftCycles (pointMorphism (c : S.X₃.X n)) (n + 1) (cochainNext n) hc 1)) =
    S.X₁.homologyπ (n + 1)
      (S.X₁.liftCycles (pointMorphism (a : S.X₁.X (n + 1))) (n + 2) (cochainNext (n + 1)) _ 1) at h
  rw [liftCyclesPoint_class, liftCyclesPoint_class] at h
  exact h

/-- Specialization to the existing relative singular connecting map. -/
theorem relativeConnecting_class_of_lift (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) (TopCat.of A) n)
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n)
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) (n + 1))
    (hb : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A).f n b = c.val)
    (ha : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f (n + 1) a.val =
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d n (n + 1) b) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting (ModuleCat.of ℚ ℚ) X A n
        (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) (TopCat.of A) n c) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) (n + 1) a :=
  connecting_class_of_lift (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainSequence (ModuleCat.of ℚ ℚ) X A)
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainSequence_shortExact (ModuleCat.of ℚ ℚ) X A) n c b a hb ha

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingRepresentative
