import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainHomotopy
import OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality

/-! # Relative Cochain Endomorphism -/

namespace OAI.AlgebraicTopology.Products.RelativeCochainEndomorphism

noncomputable section

/-!
# Restricting natural cochain endomorphisms to actual relative cochains

An endomorphism commuting with subspace restriction acts on the existing kernel
definition of relative singular cochains. A homotopy compatible with the same
restriction descends to that kernel, including its degree-zero endpoint.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [Ring R]

/-- A subspace-compatible endomorphism acts on the actual relative kernel. -/
def relativeCochainEndomorphism (M : ModuleCat.{0} R) (X : TopCat.{0}) (A : Set X)
    (f : Cohomology.Singular.Basic.singularCochains M X ⟶ Cohomology.Singular.Basic.singularCochains M X)
    (fA : Cohomology.Singular.Basic.singularCochains M (TopCat.of A) ⟶ Cohomology.Singular.Basic.singularCochains M (TopCat.of A))
    (hf : Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A ≫ fA =
      f ≫ Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A) :
    Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A ⟶ Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A :=
  kernel.map (Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A) (Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A)
    f fA hf

@[reassoc (attr := simp)]
theorem relativeCochainEndomorphism_inclusion (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X)
    (f : Cohomology.Singular.Basic.singularCochains M X ⟶ Cohomology.Singular.Basic.singularCochains M X)
    (fA : Cohomology.Singular.Basic.singularCochains M (TopCat.of A) ⟶ Cohomology.Singular.Basic.singularCochains M (TopCat.of A))
    (hf : Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A ≫ fA =
      f ≫ Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A) :
    relativeCochainEndomorphism M X A f fA hf ≫ Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A =
      Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A ≫ f :=
  kernel.lift_ι _ _ _

@[simp]
theorem relativeCochainEndomorphism_inclusion_apply (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X)
    (f : Cohomology.Singular.Basic.singularCochains M X ⟶ Cohomology.Singular.Basic.singularCochains M X)
    (fA : Cohomology.Singular.Basic.singularCochains M (TopCat.of A) ⟶ Cohomology.Singular.Basic.singularCochains M (TopCat.of A))
    (hf : Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A ≫ fA =
      f ≫ Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A) (n : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n) :
    (Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n
        ((relativeCochainEndomorphism M X A f fA hf).f n c) =
      f.f n ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n c) :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom
      (relativeCochainEndomorphism_inclusion M X A f fA hf) n) c

/-- A compatible homotopy sends each relative cochain to the relative kernel. -/
theorem relativeCochainEndomorphismHomotopy_preserves (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X)
    {f : Cohomology.Singular.Basic.singularCochains M X ⟶ Cohomology.Singular.Basic.singularCochains M X}
    {fA : Cohomology.Singular.Basic.singularCochains M (TopCat.of A) ⟶ Cohomology.Singular.Basic.singularCochains M (TopCat.of A)}
    (H : Homotopy f (𝟙 _)) (HA : Homotopy fA (𝟙 _))
    (hH : ∀ a b, H.hom a b ≫ (Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f b =
      (Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f a ≫ HA.hom a b)
    (a b : ℕ) (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X a) :
    H.hom a b ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f a c) ∈
      LinearMap.range ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f b).hom := by
  rw [Cohomology.Singular.RelativeSequence.relativeCochainInclusion_range]
  change (Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f b
      (H.hom a b ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f a c)) = 0
  have hz : (Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f a
      ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f a c) = 0 :=
    ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom (Cohomology.Singular.RelativeSequence.relativeCochainInclusion_restriction M X A) a) c
  have hn := ConcreteCategory.congr_hom (hH a b)
    ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f a c)
  change (Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f b
      (H.hom a b ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f a c)) =
    HA.hom a b ((Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f a
      ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f a c)) at hn
  rw [hn, hz, map_zero]

/-- Restrict a genuine compatible homotopy to the actual relative kernel. -/
def relativeCochainEndomorphismHomotopyId (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X)
    (f : Cohomology.Singular.Basic.singularCochains M X ⟶ Cohomology.Singular.Basic.singularCochains M X)
    (fA : Cohomology.Singular.Basic.singularCochains M (TopCat.of A) ⟶ Cohomology.Singular.Basic.singularCochains M (TopCat.of A))
    (hf : Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A ≫ fA =
      f ≫ Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A)
    (H : Homotopy f (𝟙 _)) (HA : Homotopy fA (𝟙 _))
    (hH : ∀ a b, H.hom a b ≫ (Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f b =
      (Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f a ≫ HA.hom a b) :
    Homotopy (relativeCochainEndomorphism M X A f fA hf) (𝟙 _) :=
  AlgebraicGeometry.CycleClass.Geometric.InjectiveHomotopyRestrictionBetween.Cycles.restrictHomotopyBetween
    (Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A) (Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A)
    (AlgebraicGeometry.CycleClass.Geometric.RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective M X A)
    (relativeCochainEndomorphism_inclusion M X A f fA hf)
    (by simp only [Category.id_comp, Category.comp_id])
    H (relativeCochainEndomorphismHomotopy_preserves M X A H HA hH)

/-- The descended homotopy still has the original ambient components after
the injective inclusion, so the construction preserves the actual cochains. -/
@[reassoc]
theorem relativeCochainEndomorphismHomotopyId_inclusion (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X)
    (f : Cohomology.Singular.Basic.singularCochains M X ⟶ Cohomology.Singular.Basic.singularCochains M X)
    (fA : Cohomology.Singular.Basic.singularCochains M (TopCat.of A) ⟶ Cohomology.Singular.Basic.singularCochains M (TopCat.of A))
    (hf : Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A ≫ fA =
      f ≫ Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A)
    (H : Homotopy f (𝟙 _)) (HA : Homotopy fA (𝟙 _))
    (hH : ∀ a b, H.hom a b ≫ (Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f b =
      (Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f a ≫ HA.hom a b) (a b : ℕ) :
    (relativeCochainEndomorphismHomotopyId M X A f fA hf H HA hH).hom a b ≫
        (Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f b =
      (Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f a ≫ H.hom a b :=
  AlgebraicGeometry.CycleClass.Geometric.InjectiveHomotopyRestrictionBetween.Cycles.restrictedBetweenComponent_comp _ _ _ _ _ a b

/-- A compatible homotopy to identity induces identity on relative cohomology. -/
theorem relativeCochainEndomorphism_homologyMap_eq_id (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X)
    (f : Cohomology.Singular.Basic.singularCochains M X ⟶ Cohomology.Singular.Basic.singularCochains M X)
    (fA : Cohomology.Singular.Basic.singularCochains M (TopCat.of A) ⟶ Cohomology.Singular.Basic.singularCochains M (TopCat.of A))
    (hf : Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A ≫ fA =
      f ≫ Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A)
    (H : Homotopy f (𝟙 _)) (HA : Homotopy fA (𝟙 _))
    (hH : ∀ a b, H.hom a b ≫ (Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f b =
      (Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f a ≫ HA.hom a b) (n : ℕ) :
    HomologicalComplex.homologyMap (relativeCochainEndomorphism M X A f fA hf) n =
      𝟙 ((Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).homology n) := by
  simpa only [HomologicalComplex.homologyMap_id] using
    (relativeCochainEndomorphismHomotopyId M X A f fA hf H HA hH).homologyMap_eq n

end

end OAI.AlgebraicTopology.Products.RelativeCochainEndomorphism
