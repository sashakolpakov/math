import OAI.AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexFundamentalNaturality
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

/-! # Complex Cap Diffeomorphism -/

namespace OAI.AlgebraicTopology.Duality.Poincare.ComplexCapDiffeomorphism

noncomputable section

section

/-!
# Canonical cap and compact-support evaluation under complex diffeomorphisms

The actual complex fundamental class is preserved by a complex C1
diffeomorphism. Together with relative cap naturality and the genuine
proper compact-support pullback, this gives covariance of the canonical
cap map and invariance of its cohomological evaluation pairing.
No Poincare-duality isomorphism is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexFundamentalNaturality.Cycles
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (d : ℕ) {M N : Type}
  [TopologicalSpace M] [T2Space M] [ChartedSpace (Fin d → ℂ) M]
  [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]
  [TopologicalSpace N] [T2Space N] [ChartedSpace (Fin d → ℂ) N]
  [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 N]

/-- The canonical compact fundamental class is preserved also after
transport to any equal homological degree. -/
theorem complexCompactClassInDegree_diffeomorph
    (f : Diffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M N 1)
    (n : ℕ) (hn : n = 2 * d) (K : Compacts M) (L : Compacts N)
    (hmap : ∀ x, x ∈ (K : Set M) ↔ f.toHomeomorph x ∈ (L : Set N)) :
    (AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.homeomorphSupportHomologyIso (X := TopCat.of M) (Y := TopCat.of N)
        f.toHomeomorph K L hmap n).hom
        (ComplexManifoldCap.complexCompactClassInDegree d (M := M) n hn K) =
      ComplexManifoldCap.complexCompactClassInDegree d (M := N) n hn L := by
  subst n
  exact AlgebraicGeometry.CycleClass.Geometric.ComplexFundamentalNaturality.Cycles.complexCompactFundamentalClass_diffeomorph f K L K.isCompact L.isCompact hmap

/-- Inverse-image compact supports give the actual forward map of
complementary pairs, and that map sends the canonical class to the target class. -/
theorem complexCompactClassInDegree_diffeomorph_preimage
    (f : Diffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M N 1)
    (K : Compacts N) (n : ℕ) (hn : n = 2 * d) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap
        (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
        (A := (ProperCompactSupportPullback.properCompactPreimage
          (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
          f.toHomeomorph.isProperMap K : Set M)ᶜ)
        (B := (K : Set N)ᶜ) (fun _ hx => hx) n
        (ComplexManifoldCap.complexCompactClassInDegree d (M := M) n hn
          (ProperCompactSupportPullback.properCompactPreimage
            (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
            f.toHomeomorph.isProperMap K)) =
      ComplexManifoldCap.complexCompactClassInDegree d (M := N) n hn K := by
  exact complexCompactClassInDegree_diffeomorph d f n hn
    (ProperCompactSupportPullback.properCompactPreimage
      (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
      f.toHomeomorph.isProperMap K) K (fun _ => Iff.rfl)

/-- At each compact support, proper pullback followed by canonical cap
and ordinary pushforward is the target's canonical relative cap. -/
@[reassoc]
theorem complexRelativeCap_diffeomorph
    (f : Diffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M N 1)
    (K : Compacts N) (p q : ℕ) (hpq : p + q = 2 * d) :
    ProperCompactSupportPullback.compactSupportProperStageCohomologyPullback (ModuleCat.of ℚ ℚ)
        (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
        f.toHomeomorph.isProperMap K p ≫
      SupportCapNaturality.relativeCapWithClass (TopCat.of M)
        (ProperCompactSupportPullback.properCompactPreimage
          (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
          f.toHomeomorph.isProperMap K : Set M)ᶜ p q
        (ComplexManifoldCap.complexCompactClassInDegree d (M := M) (p + q) hpq
          (ProperCompactSupportPullback.properCompactPreimage
            (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
            f.toHomeomorph.isProperMap K)) ≫
      Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ)
        (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom q =
    SupportCapNaturality.relativeCapWithClass (TopCat.of N) (K : Set N)ᶜ p q
      (ComplexManifoldCap.complexCompactClassInDegree d (M := N) (p + q) hpq K) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have hcap := SupportCapNaturality.relativeCapHomology_naturality
    (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
    (A := (ProperCompactSupportPullback.properCompactPreimage
      (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
      f.toHomeomorph.isProperMap K : Set M)ᶜ)
    (B := (K : Set N)ᶜ) (fun _ hx => hx) p q a
    (ComplexManifoldCap.complexCompactClassInDegree d (M := M) (p + q) hpq
      (ProperCompactSupportPullback.properCompactPreimage
        (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
        f.toHomeomorph.isProperMap K))
  exact hcap.trans (congrArg (SupportRelativeCap.relativeCapHomology (TopCat.of N) (K : Set N)ᶜ p q a)
    (complexCompactClassInDegree_diffeomorph_preimage d f K (p + q) hpq))

/-- Covariance of the actual canonical cap map under a complex C1
diffeomorphism, using the genuine proper pullback and continuous pushforward. -/
@[reassoc]
theorem complexManifoldCompactSupportCap_diffeomorph
    (f : Diffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M N 1)
    (p q : ℕ) (hpq : p + q = 2 * d) :
    ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
        (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
        f.toHomeomorph.isProperMap p ≫
      ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq ≫
      Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ)
        (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom q =
    ComplexManifoldCap.complexManifoldCompactSupportCap d (M := N) p q hpq := by
  apply CompactSupportColimit.compactSupportedCohomology_hom_ext (ModuleCat.of ℚ ℚ) (TopCat.of N) p
  intro K
  rw [ProperCompactSupportPullback.compactSupportCohomologyι_properPullback_assoc,
    ComplexManifoldCap.complexManifoldCompactSupportCap_stage_assoc, ComplexManifoldCap.complexManifoldCompactSupportCap_stage]
  exact complexRelativeCap_diffeomorph d f K p q hpq

/-- Elementwise form of canonical cap covariance. -/
theorem complexManifoldCompactSupportCap_diffeomorph_apply
    (f : Diffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M N 1)
    (p q : ℕ) (hpq : p + q = 2 * d)
    (b : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) p) :
    Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ)
        (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom q
        (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq
          (ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
            (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
            f.toHomeomorph.isProperMap p b)) =
      ComplexManifoldCap.complexManifoldCompactSupportCap d (M := N) p q hpq b :=
  ConcreteCategory.congr_hom (complexManifoldCompactSupportCap_diffeomorph d f p q hpq) b

/-- The actual ordinary/compact-support evaluation pairing is invariant
when both arguments are pulled back by a complex C1 diffeomorphism. -/
theorem compactSupportEvaluation_diffeomorph
    (f : Diffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M N 1)
    (p q : ℕ) (hpq : p + q = 2 * d)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) p)
    (b : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) q) :
    CompactSupportDualCohomology.compactSupportEvaluation d (M := M) p q hpq
        (Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
          (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom p a)
        (ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
          (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
          f.toHomeomorph.isProperMap q b) =
      CompactSupportDualCohomology.compactSupportEvaluation d (M := N) p q hpq a b := by
  rw [CompactSupportDualCohomology.compactSupportEvaluation_apply, CompactSupportDualCohomology.compactSupportEvaluation_apply,
    Cohomology.Singular.EvaluationNaturality.singularEvaluation_naturality,
    complexManifoldCompactSupportCap_diffeomorph_apply d f q p (by omega) b]

/-- The same covariance written with any specified actual continuous map
whose pointwise values are those of the complex diffeomorphism. -/
theorem complexManifoldCompactSupportCap_diffeomorph_map
    (f : Diffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M N 1)
    (F : TopCat.of M ⟶ TopCat.of N) (hF : ∀ x, F x = f x)
    (hproper : IsProperMap F) (p q : ℕ) (hpq : p + q = 2 * d) :
    ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ) F hproper p ≫
        ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq ≫
        Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) F q =
      ComplexManifoldCap.complexManifoldCompactSupportCap d (M := N) p q hpq := by
  have hmap : F =
      (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom := by
    ext x
    exact hF x
  subst F
  exact complexManifoldCompactSupportCap_diffeomorph d f p q hpq

/-- Pairing covariance with the actual continuous map specified explicitly;
this permits direct use with maps obtained from algebraic constructions. -/
theorem compactSupportEvaluation_diffeomorph_map
    (f : Diffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M N 1)
    (F : TopCat.of M ⟶ TopCat.of N) (hF : ∀ x, F x = f x)
    (hproper : IsProperMap F) (p q : ℕ) (hpq : p + q = 2 * d)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) p)
    (b : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) q) :
    CompactSupportDualCohomology.compactSupportEvaluation d (M := M) p q hpq
        (Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) F p a)
        (ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ) F hproper q b) =
      CompactSupportDualCohomology.compactSupportEvaluation d (M := N) p q hpq a b := by
  have hmap : F =
      (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom := by
    ext x
    exact hF x
  subst F
  exact compactSupportEvaluation_diffeomorph d f p q hpq a b

omit [T2Space M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]
  [T2Space N] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 N]

/-- Proper compact-support pullback by the underlying actual
homeomorphism is an isomorphism in every degree. -/
theorem compactSupportProperPullback_diffeomorph_isIso
    (f : Diffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M N 1) (n : ℕ) :
    IsIso (ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
      (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
      f.toHomeomorph.isProperMap n) := by
  rw [ProperCompactSupportPullback.compactSupportedCohomologyProperPullback_homeomorph]
  infer_instance

/-- Every source compact-support test class is the pullback of an actual
target test class under a complex diffeomorphism. -/
theorem compactSupportProperPullback_diffeomorph_surjective
    (f : Diffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) M N 1) (n : ℕ) :
    Function.Surjective (ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
      (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
      f.toHomeomorph.isProperMap n) := by
  let := compactSupportProperPullback_diffeomorph_isIso d f n
  exact (ConcreteCategory.bijective_of_isIso _).2

end

/-!
# Dimension and complementary-degree transport for the actual cap pairing

The ordinary degree is fixed. The compact-support degree is transported by
the specified equality after the actual proper pullback. This is the form
used when a geometric isomorphism preserves two separately defined native
model dimensions and complementary degrees.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {d e : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [T2Space M] [T2Space N]
  [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin e → ℂ) N]
  [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M] [IsManifold 𝓘(ℂ, Fin e → ℂ) 1 N]

/-- A genuine heterogeneous complex diffeomorphism preserves the actual
ordinary/compact-support pairing with the displayed complementary-degree cast. -/
theorem compactSupportEvaluation_diffeomorph_of_dimension_eq (hd : d = e)
    (f : Diffeomorph 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) M N 1)
    (k qM qN : ℕ) (hq : qN = qM)
    (hM : k + qM = 2 * d) (hN : k + qN = 2 * e)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) k)
    (b : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) qN) :
    CompactSupportDualCohomology.compactSupportEvaluation d (M := M) k qM hM
        (Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
          (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom k a)
        (eqToHom (congrArg
          (fun q => CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q) hq)
          (ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
            (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
            f.toHomeomorph.isProperMap qN b)) =
      CompactSupportDualCohomology.compactSupportEvaluation e (M := N) k qN hN a b := by
  subst e
  subst qN
  simpa only [eqToHom_refl, CategoryTheory.id_apply] using
    compactSupportEvaluation_diffeomorph d f k qM hM a b

end

end OAI.AlgebraicTopology.Duality.Poincare.ComplexCapDiffeomorphism
