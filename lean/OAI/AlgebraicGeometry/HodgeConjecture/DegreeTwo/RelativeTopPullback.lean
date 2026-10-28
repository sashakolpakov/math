import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedSourcePullback
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalSupportCup

/-! # Relative Top Pullback -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTopPullback.Constructions

noncomputable section

section

/-! The canonical top-open identification respects actual relative pullback and global restriction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

theorem relativeCohomologyOpenRestriction_top (X : TopCat.{0}) (O : Set X) (q : ℕ) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) X O ⊤ q =
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) X O q).inv := rfl

theorem relativeSourcePullbackMap_top_comparison {X Y : TopCat.{0}} (f : Y ⟶ X) (O : Opens X) (q : ℕ) :
    HomologicalComplex.homologyMap (SupportedSourcePullback.Constructions.relativeSourcePullbackMap O ⊤ f) q ≫
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) Y
        (((Opens.map f).obj O : Opens Y) : Set Y) q).hom =
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) X (O : Set X) q).hom ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
        (A := (((Opens.map f).obj O : Opens Y) : Set Y)) (B := (O : Set X)) (fun _ hx => hx) q := by
  change HomologicalComplex.homologyMap _ q ≫ HomologicalComplex.homologyMap _ q =
    HomologicalComplex.homologyMap _ q ≫ HomologicalComplex.homologyMap _ q
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 1
  dsimp only [SupportedSourcePullback.Constructions.relativeSourcePullbackMap, AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheafTopIso]
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp, AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp]
  congr 1

end

/-! The two-support cup under the canonical top-open comparison is the original global cup. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

theorem twoSupportCup_top_comparison (X : TopCat.{0}) (C O : Opens X) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (C : Set X) p) :
    ModuleCat.ofHom (SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of (⊤ : Opens X))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) ⊤) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) ⊤)
      (C.isOpen.preimage continuous_subtype_val) (O.isOpen.preimage continuous_subtype_val) p q
      (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) X (C : Set X) ⊤ p a)) ≫
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) X ((C ⊔ O : Opens X) : Set X) (p+q)).hom =
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) X (O : Set X) q).hom ≫
      ModuleCat.ofHom (SupportCup.Constructions.twoSupportCohomologyCup X (C : Set X) (O : Set X) C.isOpen O.isOpen p q a) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  let eC := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) X (C : Set X) p
  let eO := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) X (O : Set X) q
  let eT := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) X ((C ⊔ O : Opens X) : Set X) (p+q)
  have hn := SupportCup.Constructions.twoSupportCohomologyCup_naturality X (C : Set X) (O : Set X) C.isOpen O.isOpen p q
    (Opens.inclusionTopIso X).inv
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) ⊤) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) ⊤)
    (C.isOpen.preimage continuous_subtype_val) (O.isOpen.preimage continuous_subtype_val)
    (fun _ hx => hx) (fun _ hx => hx)
    (eC.inv a) b
  change SupportCup.Constructions.twoSupportCohomologyCup X (C : Set X) (O : Set X) C.isOpen O.isOpen p q
      (eC.hom (eC.inv a)) (eO.hom b) =
    eT.hom (SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of (⊤ : Opens X))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) ⊤) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) ⊤)
      (C.isOpen.preimage continuous_subtype_val) (O.isOpen.preimage continuous_subtype_val) p q (eC.inv a) b) at hn
  rw [eC.inv_hom_id_apply] at hn
  exact hn.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTopPullback.Constructions
