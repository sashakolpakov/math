import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.RepresentativeAddition

/-! # Tensor Gauge Transitions -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.DivisorClass.Chern.Holomorphic.TensorGaugeTransitions

/-! Actual local holomorphic unit gauges compare the chosen sum bundle with the product frames. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem sheafLocalLift_add_difference_image {X : TopCat.{0}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
    {a b c : S.X₃.obj.obj (op (⊤ : Opens X))}
    (la : Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover S.g a) (lb : Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover S.g b) (lc : Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover S.g c)
    (r : S.X₂.obj.obj (op (⊤ : Opens X))) (hr : S.g.hom.app (op (⊤ : Opens X)) r = c - (a + b))
    (W : Opens X) (i : X) (ha : W ≤ la.domain i) (hb : W ≤ lb.domain i) (hc : W ≤ lc.domain i) :
    S.g.hom.app (op W) (Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ hc (lc.section_ i) -
      (Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ ha (la.section_ i) + Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ hb (lb.section_ i)) -
        Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ le_top r) = 0 := by
  simp only [map_sub, map_add, Chern.Sheaf.TransitionCocycle.sheafSectionMap_restrict, la.image, lb.image, lc.image, hr]
  change Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₃ hc (Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₃ le_top c) -
    (Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₃ ha (Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₃ le_top a) +
      Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₃ hb (Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₃ le_top b)) -
        (Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₃ le_top c -
          (Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₃ le_top a + Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₃ le_top b)) = 0
  rw [Chern.Sheaf.TransitionCocycle.sheafSectionRestrict_comp, Chern.Sheaf.TransitionCocycle.sheafSectionRestrict_comp, Chern.Sheaf.TransitionCocycle.sheafSectionRestrict_comp]
  abel

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]

def holomorphicTensorDomain (u v : Connecting.holomorphicUnitCohomology E M) (i : M) : Opens M :=
  CohomologyTransitions.holomorphicCohomologyDomain E M (u + v) i ⊓
    (CohomologyTransitions.holomorphicCohomologyDomain E M u i ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M v i)

theorem holomorphicTensorDomain_mem (u v : Connecting.holomorphicUnitCohomology E M) (x : M) :
    x ∈ holomorphicTensorDomain E M u v x :=
  ⟨(CohomologyTransitions.holomorphicCohomologyLocalLifts E M (u + v)).mem_domain x,
    (CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x, (CohomologyTransitions.holomorphicCohomologyLocalLifts E M v).mem_domain x⟩

def holomorphicTensorLocalDifference (u v : Connecting.holomorphicUnitCohomology E M) (i : M) :
    (Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence (Sheaves.holomorphicUnitsSheaf E M)).X₂.obj.obj (op (holomorphicTensorDomain E M u v i)) :=
  Chern.Sheaf.TransitionCocycle.sheafSectionRestrict (Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence (Sheaves.holomorphicUnitsSheaf E M)).X₂ inf_le_left
      ((CohomologyTransitions.holomorphicCohomologyLocalLifts E M (u + v)).section_ i) -
    (Chern.Sheaf.TransitionCocycle.sheafSectionRestrict (Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence (Sheaves.holomorphicUnitsSheaf E M)).X₂
      (inf_le_right.trans inf_le_left) ((CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).section_ i) +
    Chern.Sheaf.TransitionCocycle.sheafSectionRestrict (Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence (Sheaves.holomorphicUnitsSheaf E M)).X₂
      (inf_le_right.trans inf_le_right) ((CohomologyTransitions.holomorphicCohomologyLocalLifts E M v).section_ i)) -
    Chern.Sheaf.TransitionCocycle.sheafSectionRestrict (Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence (Sheaves.holomorphicUnitsSheaf E M)).X₂ le_top
      (RepresentativeAddition.holomorphicRepresentativeAddLift E M u v)

theorem holomorphicTensorLocalDifference_image (u v : Connecting.holomorphicUnitCohomology E M) (i : M) :
    (Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence (Sheaves.holomorphicUnitsSheaf E M)).g.hom.app (op (holomorphicTensorDomain E M u v i))
      (holomorphicTensorLocalDifference E M u v i) = 0 :=
  sheafLocalLift_add_difference_image (CohomologyTransitions.holomorphicCohomologyLocalLifts E M u)
    (CohomologyTransitions.holomorphicCohomologyLocalLifts E M v) (CohomologyTransitions.holomorphicCohomologyLocalLifts E M (u + v))
    (RepresentativeAddition.holomorphicRepresentativeAddLift E M u v) (RepresentativeAddition.holomorphicRepresentativeAddLift_spec E M u v)
    (holomorphicTensorDomain E M u v i) i (inf_le_right.trans inf_le_left)
    (inf_le_right.trans inf_le_right) inf_le_left

theorem exists_holomorphicTensorGauge (u v : Connecting.holomorphicUnitCohomology E M) (i : M) :
    ∃ s : (Sheaves.holomorphicUnitsSheaf E M).obj.obj (op (holomorphicTensorDomain E M u v i)),
      (Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence (Sheaves.holomorphicUnitsSheaf E M)).f.hom.app (op (holomorphicTensorDomain E M u v i)) s =
        holomorphicTensorLocalDifference E M u v i :=
  TopCat.Sheaf.sections_exact_of_left_exact
    (Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence_shortExact (Sheaves.holomorphicUnitsSheaf E M)).exact
    (Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence_shortExact (Sheaves.holomorphicUnitsSheaf E M)).mono_f _
    (holomorphicTensorLocalDifference_image E M u v i)

def holomorphicTensorGauge (u v : Connecting.holomorphicUnitCohomology E M) (i : M) :
    (Exponential.HolomorphicFunction (E := E) (M := holomorphicTensorDomain E M u v i))ˣ :=
  Additive.toMul (Classical.choose (exists_holomorphicTensorGauge E M u v i))

theorem holomorphicTensorGauge_map (u v : Connecting.holomorphicUnitCohomology E M) (i : M) :
    (Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence (Sheaves.holomorphicUnitsSheaf E M)).f.hom.app (op (holomorphicTensorDomain E M u v i))
      (Additive.ofMul (holomorphicTensorGauge E M u v i)) = holomorphicTensorLocalDifference E M u v i :=
  Classical.choose_spec (exists_holomorphicTensorGauge E M u v i)

end AlgebraicGeometry.DivisorClass.Chern.Holomorphic.TensorGaugeTransitions

namespace AlgebraicGeometry.DivisorClass.Chern

/-! The actual sum-bundle transitions are product transitions conjugated by the constructed local gauges. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section Sheaf

variable {X : TopCat.{0}} {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
  (hS : S.ShortExact) {a b c : S.X₃.obj.obj (op (⊤ : Opens X))}

def Sheaf.CohomologyLifts.SheafLocalLiftCover.transitionOnOpen (l : Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover S.g a)
    (W : Opens X) (i j : X) (hi : W ≤ l.domain i) (hj : W ≤ l.domain j) : S.X₁.obj.obj (op W) :=
  Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₁ (le_inf hi hj) (l.transition hS i j)

theorem Sheaf.CohomologyLifts.SheafLocalLiftCover.transitionOnOpen_map (l : Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover S.g a)
    (W : Opens X) (i j : X) (hi : W ≤ l.domain i) (hj : W ≤ l.domain j) :
    S.f.hom.app (op W) (l.transitionOnOpen hS W i j hi hj) =
      Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ hj (l.section_ j) - Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ hi (l.section_ i) := by
  rw [Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover.transitionOnOpen, Chern.Sheaf.TransitionCocycle.sheafSectionMap_restrict, Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover.transition_map, Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover.difference, map_sub,
    Chern.Sheaf.TransitionCocycle.sheafSectionRestrict_comp, Chern.Sheaf.TransitionCocycle.sheafSectionRestrict_comp]

structure Holomorphic.TensorGaugeTransitions.SheafLocalTensorGauge (la : Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover S.g a) (lb : Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover S.g b)
    (lc : Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover S.g c) (r : S.X₂.obj.obj (op (⊤ : Opens X))) where
  domain : X → Opens X
  le_a : ∀ i, domain i ≤ la.domain i
  le_b : ∀ i, domain i ≤ lb.domain i
  le_c : ∀ i, domain i ≤ lc.domain i
  gauge : ∀ i, S.X₁.obj.obj (op (domain i))
  image : ∀ i, S.f.hom.app (op (domain i)) (gauge i) =
    Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ (le_c i) (lc.section_ i) -
      (Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ (le_a i) (la.section_ i) + Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ (le_b i) (lb.section_ i)) -
        Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₂ le_top r

theorem Holomorphic.TensorGaugeTransitions.SheafLocalTensorGauge.transition
    {la : Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover S.g a} {lb : Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover S.g b} {lc : Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover S.g c}
    {r : S.X₂.obj.obj (op (⊤ : Opens X))} (G : Holomorphic.TensorGaugeTransitions.SheafLocalTensorGauge la lb lc r)
    (W : Opens X) (i j : X) (hi : W ≤ G.domain i) (hj : W ≤ G.domain j) :
    lc.transitionOnOpen hS W i j (hi.trans (G.le_c i)) (hj.trans (G.le_c j)) +
      Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₁ hi (G.gauge i) =
    Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₁ hj (G.gauge j) +
      la.transitionOnOpen hS W i j (hi.trans (G.le_a i)) (hj.trans (G.le_a j)) +
      lb.transitionOnOpen hS W i j (hi.trans (G.le_b i)) (hj.trans (G.le_b j)) := by
  have : Mono S.f := hS.mono_f
  apply Chern.Sheaf.TransitionCocycle.sheafMono_section_injective S.f W
  simp only [map_add, Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover.transitionOnOpen_map, Chern.Sheaf.TransitionCocycle.sheafSectionMap_restrict,
    G.image, map_sub, Chern.Sheaf.TransitionCocycle.sheafSectionRestrict_comp]
  abel

end Sheaf

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]

def Holomorphic.TensorGaugeTransitions.holomorphicTensorGaugeData (u v : Holomorphic.Connecting.holomorphicUnitCohomology E M) :
    Holomorphic.TensorGaugeTransitions.SheafLocalTensorGauge (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u) (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M v)
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M (u + v)) (Holomorphic.RepresentativeAddition.holomorphicRepresentativeAddLift E M u v) where
  domain := Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain E M u v
  le_a _ := inf_le_right.trans inf_le_left
  le_b _ := inf_le_right.trans inf_le_right
  le_c _ := inf_le_left
  gauge i := Additive.ofMul (Holomorphic.TensorGaugeTransitions.holomorphicTensorGauge E M u v i)
  image := Holomorphic.TensorGaugeTransitions.holomorphicTensorGauge_map E M u v

theorem Holomorphic.TensorGaugeTransitions.holomorphicTensorGauge_transition (u v : Holomorphic.Connecting.holomorphicUnitCohomology E M) (i j x : M)
    (hi : x ∈ Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain E M u v i) (hj : x ∈ Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain E M u v j) :
    (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M (u + v) i j).val ⟨x, hi.1, hj.1⟩ *
      (Holomorphic.TensorGaugeTransitions.holomorphicTensorGauge E M u v i).val ⟨x, hi⟩ =
    (Holomorphic.TensorGaugeTransitions.holomorphicTensorGauge E M u v j).val ⟨x, hj⟩ *
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hi.2.1, hj.2.1⟩ *
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M v i j).val ⟨x, hi.2.2, hj.2.2⟩ :=
  congrArg (fun s : (Holomorphic.Sheaves.holomorphicUnitsSheaf E M).obj.obj
    (op (Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain E M u v i ⊓ Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain E M u v j)) =>
      ((Additive.toMul s : (Holomorphic.Exponential.HolomorphicFunction (E := E)
        (M := ↥(Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain E M u v i ⊓ Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain E M u v j)))ˣ).val) ⟨x, hi, hj⟩)
    ((Holomorphic.TensorGaugeTransitions.holomorphicTensorGaugeData E M u v).transition
      (Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence_shortExact (Holomorphic.Sheaves.holomorphicUnitsSheaf E M))
      (Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain E M u v i ⊓ Holomorphic.TensorGaugeTransitions.holomorphicTensorDomain E M u v j) i j inf_le_left inf_le_right)

end AlgebraicGeometry.DivisorClass.Chern

end

end OAI
